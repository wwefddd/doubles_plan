import sys
sys.stdout.reconfigure(encoding='utf-8')

import asyncio
from fastapi import FastAPI, Request, WebSocket, WebSocketDisconnect
from fastapi.templating import Jinja2Templates
from pydantic import BaseModel
import uvicorn
import os
import time
import sqlite3
import random
import hashlib
from itertools import product, combinations
from collections import defaultdict
from functools import lru_cache
from typing import List, Set, Tuple, Dict
from fastapi.middleware.cors import CORSMiddleware
app = FastAPI()

# 💡 [STEP 1] CORS 설정: 프론트엔드(GitHub Pages)에서 오라클 서버로의 접근을 허용
origins = [
    "http://localhost:8000",
    "http://127.0.0.1:8000",
    "https://wwefddd.github.io" # 최종 배포될 깃허브 페이지 주소
]

app.add_middleware(
    CORSMiddleware,
    allow_origins=origins,
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)


templates = Jinja2Templates(directory="templates")

BLACK_CARDS = {1, 2, 10, 11, 12}
RED_CARDS = {3, 4, 5, 6, 7, 8, 9}
TOTAL_DECK = BLACK_CARDS | RED_CARDS

class HistoryItem(BaseModel):
    oop: str
    ip: str
    score_p0: int

class GTOReq(BaseModel):
    player: str
    current_round: int
    hand: List[int]
    color: str
    history: List[HistoryItem]

class ExactEVReq(BaseModel):
    p0_hand: List[int]
    p1_hand: List[int]
    current_round: int
    history: List[HistoryItem]

def get_strategy_from_db(key: str) -> str:
    with sqlite3.connect("gto_data.db") as conn:
        c = conn.cursor()
        c.execute("SELECT strat FROM strategy WHERE state_key=?", (key,))
        row = c.fetchone()
        return row[0] if row else None

@lru_cache(maxsize=100000)
def get_strategy_cached(key: str) -> str:
    return get_strategy_from_db(key)

# GTO 탐색용 고정 득점 (내부 분석용)
class CardScorer:
    @staticmethod
    def get_score(p0_card: int, p1_card: int) -> int:
        if p0_card == 2 * p1_card: return 2
        if p1_card == 2 * p0_card: return -2
        if p0_card > 2 * p1_card: return -1
        if p1_card > 2 * p0_card: return 1
        if p0_card > p1_card: return 1
        else: return -1

# 실전 게임용 세트별 점수 계산기
def get_actual_game_score(p0_card: int, p1_card: int, current_set: int) -> Tuple[int, int]:
    if p0_card == p1_card: return 0, 0
    
    high = max(p0_card, p1_card)
    low = min(p0_card, p1_card)
    is_p0_high = (p0_card > p1_card)
    
    if high == low * 2:
        win_type = 'double'
        winner_is_p0 = is_p0_high
    elif high > low * 2:
        win_type = 'comeback'
        winner_is_p0 = not is_p0_high
    else:
        win_type = 'basic'
        winner_is_p0 = is_p0_high
        
    pts = 0
    if current_set == 1:
        pts = 1
    elif current_set == 2:
        pts = 2 if win_type == 'double' else 1
    else:
        pts = 4 if win_type == 'double' else 2
        
    return (pts, 0) if winner_is_p0 else (0, pts)

class UniverseGenerator:
    @classmethod
    def generate_all_worlds(cls, player: str, current_hand: List[int], raw_history: List[HistoryItem]) -> List[List[Tuple[int, int]]]:
        known_in_history = set()
        for h in raw_history:
            if h.oop != '?': known_in_history.add(int(h.oop))
            if h.ip != '?': known_in_history.add(int(h.ip))
        
        available_for_q = TOTAL_DECK - set(current_hand) - known_in_history
        local_universes = []
        for round_idx, h in enumerate(raw_history):
            is_p0_oop = (round_idx % 2 == 0) 
            valid_pairs = []
            oop_pool = list(available_for_q) if h.oop == '?' else [int(h.oop)]
            ip_pool = list(available_for_q) if h.ip == '?' else [int(h.ip)]
            
            for o_c, i_c in product(oop_pool, ip_pool):
                if o_c == i_c: continue
                if h.oop != '?' and h.ip != '?':
                    valid_pairs.append((o_c, i_c))
                    continue
                
                p0_card = o_c if is_p0_oop else i_c
                p1_card = i_c if is_p0_oop else o_c
                
                if CardScorer.get_score(p0_card, p1_card) == h.score_p0:
                    valid_pairs.append((o_c, i_c))
            
            if not valid_pairs: return [] 
            local_universes.append(valid_pairs)

        all_scenarios = []
        for scenario in product(*local_universes):
            used_in_scenario = []
            for pair in scenario: used_in_scenario.extend(pair)
            if len(set(used_in_scenario)) == len(used_in_scenario):
                if not (set(used_in_scenario) & set(current_hand)):
                    all_scenarios.append(list(scenario))
        return all_scenarios

# ==========================================
# 🎮 PvP 실시간 멀티플레이 로직
# ==========================================
class DBRoom:
    def __init__(self, room_id):
        self.room_id = room_id
        self.players = {}
        self.p1_id = None
        self.p2_id = None
        self.p1_name = "P1"
        self.p2_name = "P2"
        
        self.current_set = 1
        self.current_round = 1
        self.p1_score = 0
        self.p2_score = 0
        
        self.p1_hand = []
        self.p2_hand = []
        self.history = [] 
        
        self.oop_card = None
        self.game_over = False
        self.transitioning = False # 💡 스왑 버그 방지용 전환 락
        self.msg = "상대방을 기다리는 중..."

    def start_set(self):
        b_pool = list(BLACK_CARDS)
        r_pool = list(RED_CARDS)
        random.shuffle(b_pool)
        random.shuffle(r_pool)
        
        self.p1_hand = b_pool[0:2] + r_pool[0:3]
        self.p2_hand = b_pool[2:4] + r_pool[3:6]
        
        self.current_round = 1
        self.history = []
        self.oop_card = None
        self.transitioning = False
        self.msg = f"{self.current_set}세트 시작! (총 4세트)"

    def handle_action(self, client_id, action_card):
        if self.game_over: return "게임이 이미 종료되었습니다.", False
        if len(self.players) < 2: return "상대방이 접속하지 않았습니다.", False
        if self.transitioning: return "다음 세트를 준비 중입니다.", False

        p1_is_p0 = (self.current_set % 2 != 0)
        my_is_p0 = (client_id == self.p1_id) if p1_is_p0 else (client_id == self.p2_id)
        is_p0_oop = (self.current_round % 2 != 0)
        my_is_oop = (my_is_p0 == is_p0_oop)

        my_turn = (self.oop_card is None) if my_is_oop else (self.oop_card is not None)
        if not my_turn: return "당신의 턴이 아닙니다.", False

        hand = self.p1_hand if client_id == self.p1_id else self.p2_hand
        if action_card not in hand: return "유효하지 않은 카드입니다.", False

        hand.remove(action_card)
        
        if self.oop_card is None:
            self.oop_card = action_card
            self.msg = "선공이 카드를 냈습니다! 후공 차례입니다."
        else:
            ip_card = action_card
            p0_card = self.oop_card if is_p0_oop else ip_card
            p1_card = ip_card if is_p0_oop else self.oop_card
            
            p0_pts, p1_pts = get_actual_game_score(p0_card, p1_card, self.current_set)
            gto_score_p0 = CardScorer.get_score(p0_card, p1_card)
            
            if p1_is_p0:
                self.p1_score += p0_pts
                self.p2_score += p1_pts
            else:
                self.p2_score += p0_pts
                self.p1_score += p1_pts
                
            self.history.append({'oop': self.oop_card, 'ip': ip_card, 'score_p0': gto_score_p0})
            
            win_msg = f"P0 승리 (+{p0_pts}점)" if p0_pts > 0 else (f"P1 승리 (+{p1_pts}점)" if p1_pts > 0 else "무승부")
            self.msg = f"라운드 종료! [ P0({p0_card}) vs P1({p1_card}) ] ➔ {win_msg}"
            
            self.oop_card = None
            self.current_round += 1
            
            if self.current_round > 5:
                self.current_round = 5 # 💡 디스플레이 강제 고정으로 UI 꼬임 방지
                if self.current_set >= 4:
                    self.game_over = True
                    winner = self.p1_name if self.p1_score > self.p2_score else (self.p2_name if self.p2_score > self.p1_score else "무승부")
                    self.msg = f"게임 종료! 최종 승자는 {winner} 입니다!"
                    return None, False
                else:
                    self.transitioning = True
                    self.msg += " (2초 뒤 다음 세트 시작)"
                    return None, True
        return None, False

    def get_state_for_client(self, client_id):
        is_p1 = (client_id == self.p1_id)
        p1_is_p0 = (self.current_set % 2 != 0)
        
        my_name = self.p1_name if is_p1 else self.p2_name
        opp_name = self.p2_name if is_p1 else self.p1_name
        my_score = self.p1_score if is_p1 else self.p2_score
        opp_score = self.p2_score if is_p1 else self.p1_score
        
        my_hand = self.p1_hand if is_p1 else self.p2_hand
        opp_hand_count = len(self.p2_hand) if is_p1 else len(self.p1_hand)
        
        my_is_p0 = (is_p1 and p1_is_p0) or (not is_p1 and not p1_is_p0)
        is_p0_oop = (self.current_round % 2 != 0)
        my_is_oop = (my_is_p0 == is_p0_oop)
        
        my_turn = False
        oop_color_show = None
        
        if len(self.players) == 2 and not self.game_over:
            if self.oop_card is None:
                my_turn = my_is_oop
            else:
                my_turn = not my_is_oop
                if my_turn:
                    oop_color_show = "Black" if self.oop_card in BLACK_CARDS else "Red"

        return {
            "type": "state", "set": self.current_set, "round": self.current_round,
            "my_name": my_name, "opp_name": opp_name, "my_score": my_score, "opp_score": opp_score,
            "my_hand": my_hand, "opp_hand_count": opp_hand_count, "oop_color": oop_color_show,
            "history": self.history, "msg": self.msg, "my_turn": my_turn, "my_is_p0": my_is_p0,
            "my_is_oop": my_is_oop, "game_over": self.game_over, "waiting": len(self.players) < 2,
            "transitioning": getattr(self, 'transitioning', False)
        }

class RoomManager:
    def __init__(self):
        self.rooms: Dict[str, DBRoom] = {}
    def get_room(self, room_id: str) -> DBRoom:
        if room_id not in self.rooms: self.rooms[room_id] = DBRoom(room_id)
        return self.rooms[room_id]
    async def broadcast(self, room: DBRoom):
        for cid, ws in room.players.items():
            try: await ws.send_json(room.get_state_for_client(cid))
            except: pass

manager = RoomManager()

@app.websocket("/ws_pvp/{room_id}/{client_id}/{nickname}")
async def websocket_endpoint(websocket: WebSocket, room_id: str, client_id: str, nickname: str):
    await websocket.accept()
    room = manager.get_room(room_id)
    
    if client_id not in room.players:
        if room.p1_id is None:
            room.p1_id = client_id; room.p1_name = nickname; room.players[client_id] = websocket
        elif room.p2_id is None:
            room.p2_id = client_id; room.p2_name = nickname; room.players[client_id] = websocket
            room.start_set()
        else:
            await websocket.send_json({"error": "방이 꽉 찼습니다."}); await websocket.close(); return
            
    await manager.broadcast(room)

    try:
        while True:
            data = await websocket.receive_json()
            if data.get("type") == "move":
                err, should_transition = room.handle_action(client_id, int(data.get("card")))
                if err: 
                    await websocket.send_json({"error": err})
                else: 
                    await manager.broadcast(room)
                    # 💡 스왑 버그 해결: 2초간 5라운드 결과를 보여준 뒤에 조심스럽게 세트 전환!
                    if should_transition:
                        await asyncio.sleep(2)
                        room.current_set += 1
                        room.transitioning = False
                        room.start_set()
                        await manager.broadcast(room)
    except WebSocketDisconnect:
        if client_id in room.players:
            del room.players[client_id]
            if room.p1_id == client_id: room.p1_id = None
            if room.p2_id == client_id: room.p2_id = None
            room.msg = "상대방이 연결을 끊었습니다."
            await manager.broadcast(room)

# ==========================================
# 라우팅 및 GTO API
# ==========================================
@app.get("/")
def home(request: Request):
    return templates.TemplateResponse(request=request, name="index.html")

@app.get("/solver")
def solver_page(request: Request):
    return templates.TemplateResponse(request=request, name="index_db.html")

@app.post("/api/search_db")
def search_db(req: GTOReq):
    start_calc = time.time()
    hand_str = "[" + ",".join(map(str, sorted(req.hand))) + "]"
    is_oop = (req.current_round % 2 != 0) if req.player == "P0" else (req.current_round % 2 == 0)

    has_question_mark = any(h.oop == '?' or h.ip == '?' for h in req.history)
    
    if not has_question_mark:
        hist_str = "".join([f"[{h.oop}vs{h.ip}]" for h in req.history])
        search_key = f"{req.player}_OOP_Hand:{hand_str}_Hist:{hist_str}" if is_oop else f"{req.player}_IP_Hand:{hand_str}_OOPColor:{req.color}_Hist:{hist_str}"
        strategy = get_strategy_cached(search_key)
        calc_time = time.time() - start_calc
        if strategy: return {"status": "success", "strategy": strategy, "msg": "⚡ 다이렉트 DB 검색 완료", "calc_time": f"{calc_time*1000:.2f}ms"}
        return {"status": "not_found", "error": "해당 상황을 찾을 수 없습니다."}

    scenarios = UniverseGenerator.generate_all_worlds(req.player, req.hand, req.history)
    if not scenarios: return {"status": "not_found", "error": "수학적으로 모순된 상황입니다."}

    total_probabilities = defaultdict(float)
    valid_universe_count = 0

    for scenario in scenarios:
        hist_str = "".join([f"[{p0_c}vs{p1_c}]" for p0_c, p1_c in scenario])
        search_key = f"{req.player}_OOP_Hand:{hand_str}_Hist:{hist_str}" if is_oop else f"{req.player}_IP_Hand:{hand_str}_OOPColor:{req.color}_Hist:{hist_str}"
        strategy_str = get_strategy_cached(search_key)
        if strategy_str:
            valid_universe_count += 1
            for act in strategy_str.split(","):
                if ":" in act:
                    card_raw, prob_raw = act.split(":")
                    total_probabilities[int(card_raw)] += float(prob_raw)

    if valid_universe_count == 0: return {"status": "not_found", "error": "데이터가 없습니다."}

    final_strategy_list = []
    for card in sorted(total_probabilities.keys()):
        avg_prob = total_probabilities[card] / valid_universe_count
        final_strategy_list.append(f"{card}:{avg_prob:.4f}")
    
    seed_string = f"{req.player}_{req.current_round}_{hand_str}_{req.color}_" + "".join([f"{h.oop}{h.ip}" for h in req.history])
    seed_val = int(hashlib.md5(seed_string.encode()).hexdigest(), 16) % (10**8)
    random.seed(seed_val)
    random.seed()
    
    return {"status": "success", "strategy": ",".join(final_strategy_list), "msg": f"⚠️ {valid_universe_count}개의 평행우주 평균 전략", "calc_time": f"{(time.time() - start_calc)*1000:.2f}ms"}

def calculate_exact_ev_recursive(p0_curr: List[int], p1_curr: List[int], r: int, curr_oop_idx: int, sim_hist: List[Tuple[int, int]]) -> float:
    if r > 5: return 0.0

    acting_player = curr_oop_idx
    acting_hand = p0_curr if acting_player == 0 else p1_curr
    hist_str = "".join([f"[{o}vs{i}]" for o, i in sim_hist])
    hand_str = "[" + ",".join(map(str, sorted(acting_hand))) + "]"
    key0 = f"P{acting_player}_OOP_Hand:{hand_str}_Hist:{hist_str}"

    strat_str = get_strategy_cached(key0)
    oop_moves = []
    if strat_str:
        for act in strat_str.split(","):
            c, p = act.split(":")
            oop_moves.append((int(c), float(p)))
    else:
        oop_moves = [(c, 1.0 / len(acting_hand)) for c in acting_hand]

    expected_value_sum = 0.0

    for oop_card, oop_prob in oop_moves:
        next_p0 = p0_curr.copy(); next_p1 = p1_curr.copy()
        if acting_player == 0: next_p0.remove(oop_card)
        else: next_p1.remove(oop_card)

        ip_player = 1 - curr_oop_idx
        ip_hand = next_p0 if ip_player == 0 else next_p1
        opp_color = "Black" if oop_card in BLACK_CARDS else "Red"

        hand_str_ip = "[" + ",".join(map(str, sorted(ip_hand))) + "]"
        key1 = f"P{ip_player}_IP_Hand:{hand_str_ip}_OOPColor:{opp_color}_Hist:{hist_str}"

        strat_str_ip = get_strategy_cached(key1)
        ip_moves = []
        if strat_str_ip:
            for act in strat_str_ip.split(","):
                c, p = act.split(":")
                ip_moves.append((int(c), float(p)))
        else:
            ip_moves = [(c, 1.0 / len(ip_hand)) for c in ip_hand]

        for ip_card, ip_prob in ip_moves:
            next2_p0 = next_p0.copy(); next2_p1 = next_p1.copy()
            if ip_player == 0: next2_p0.remove(ip_card)
            else: next2_p1.remove(ip_card)

            p0_card = oop_card if curr_oop_idx == 0 else ip_card
            p1_card = ip_card if curr_oop_idx == 0 else oop_card
            score = CardScorer.get_score(p0_card, p1_card)

            next_hist = sim_hist + [(oop_card, ip_card)]
            future_ev = calculate_exact_ev_recursive(next2_p0, next2_p1, r + 1, 1 - curr_oop_idx, next_hist)
            expected_value_sum += oop_prob * ip_prob * (score + future_ev)

    return expected_value_sum

@app.post("/api/calc_exact_ev")
def calc_exact_ev(req: ExactEVReq):
    start_calc = time.time()
    if len(req.p0_hand) != 6 - req.current_round or len(req.p1_hand) != 6 - req.current_round:
        return {"status": "error", "error": f"현재 라운드({req.current_round}R)에 맞게 카드를 설정해주세요."}
    
    sim_hist_base = []
    for h in req.history:
        if h.oop == '?' or h.ip == '?': return {"status": "error", "error": "히스토리에 '?'가 없어야 합니다."}
        sim_hist_base.append((int(h.oop), int(h.ip)))

    curr_oop_idx = 0 if (req.current_round % 2 != 0) else 1
    exact_expected_value = calculate_exact_ev_recursive(req.p0_hand, req.p1_hand, req.current_round, curr_oop_idx, sim_hist_base)
    calc_time = time.time() - start_calc
    
    return {"status": "success", "ev": f"{exact_expected_value:+.2f}", "calc_time": f"{calc_time*1000:.2f}ms"}

if __name__ == "__main__":
    uvicorn.run(app, host="0.0.0.0", port=8000)