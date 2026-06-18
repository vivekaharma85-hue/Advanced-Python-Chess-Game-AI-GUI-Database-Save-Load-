import tkinter as tk
from tkinter import messagebox, simpledialog, filedialog, colorchooser
import copy
import pickle
import os
import random
import math
import sqlite3
from collections import defaultdict
from datetime import datetime

# -----------------------
# Full Chess — Responsive UI, AI, DB, Piece Styles & Custom Colors
# Single-file, no external images required (uses Unicode or canvas-drawn pieces)
# -----------------------

ROWS, COLS = 8, 8
WHITE, BLACK = 'W', 'B'
PIECE_ORDER = ["R", "N", "B", "Q", "K", "B", "N", "R"]
UNICODE = {
    ("W","K"): "♔", ("B","K"): "♚",
    ("W","Q"): "♕", ("B","Q"): "♛",
    ("W","R"): "♖", ("B","R"): "♜",
    ("W","B"): "♗", ("B","B"): "♝",
    ("W","N"): "♘", ("B","N"): "♞",
    ("W","P"): "♙", ("B","P"): "♟",
}

# UI layout params
CELL = 72
MARGIN = 20

# Game state
pieces = {}
turn = WHITE
castling_rights = {"W_K":True,"W_Q":True,"B_K":True,"B_Q":True}
en_passant = None
halfmove_clock = 0
fullmove_number = 1
history = []
position_counts = defaultdict(int)

selected_sq = None
legal_moves_cache = []
moves_list = []
play_mode = 'human_white'  # 'human_white','human_black','pvp'

# AI settings
ROOT_CANDIDATE_MOVES = 12
transposition_table = {}
PIECE_VALUES = {'K':900, 'Q':90, 'R':50, 'B':30, 'N':30, 'P':10}

# DB
DB_FILE = 'chess.db'

# Piece style settings (persisted)
piece_style = 'unicode'  # options: 'unicode', 'minimal', 'high_contrast'
minimal_white_color = '#ffffff'
minimal_black_color = '#000000'
highc_white = '#ffffff'
highc_black = '#000000'

# -----------------------
# Database functions
# -----------------------
def init_db():
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    c.execute('''
        CREATE TABLE IF NOT EXISTS games (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            moves TEXT,
            winner TEXT,
            created_at TEXT
        )
    ''')
    c.execute('''
        CREATE TABLE IF NOT EXISTS settings (
            k TEXT PRIMARY KEY,
            v TEXT
        )
    ''')
    conn.commit()
    conn.close()

def save_game_record(moves, winner):
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    c.execute('INSERT INTO games (moves, winner, created_at) VALUES (?, ?, ?)',
              (" ".join(moves), winner, datetime.now().isoformat()))
    conn.commit()
    conn.close()

def fetch_all_games():
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    c.execute('SELECT id, moves, winner, created_at FROM games ORDER BY id DESC')
    rows = c.fetchall()
    conn.close()
    return rows

def save_setting(k, v):
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    c.execute('INSERT OR REPLACE INTO settings (k,v) VALUES (?,?)', (k, v))
    conn.commit()
    conn.close()

def load_setting(k, default=None):
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    c.execute('SELECT v FROM settings WHERE k=?', (k,))
    row = c.fetchone()
    conn.close()
    return row[0] if row else default

# -----------------------
# Tkinter setup
# -----------------------
root = tk.Tk()
root.title('Full Chess — Responsive + Styles')
root.geometry('1000x700')

root.grid_columnconfigure(0, weight=3)
root.grid_columnconfigure(1, weight=1)
root.grid_rowconfigure(0, weight=1)

canvas = tk.Canvas(root, bg='white')
canvas.grid(row=0, column=0, sticky='nsew', padx=(MARGIN//2, MARGIN//2), pady=(MARGIN//2, MARGIN//2))

sidebar = tk.Frame(root)
sidebar.grid(row=0, column=1, sticky='nsew')

turn_label = tk.Label(sidebar, text='Turn: White', font=('Arial', 12))
turn_label.pack(pady=6)

btn_frame = tk.Frame(sidebar)
btn_frame.pack(pady=6)

ai_var = tk.BooleanVar(value=True)
depth_var = tk.IntVar(value=2)

status_label = tk.Label(sidebar, text='', fg='darkgreen')
status_label.pack(pady=6)

btn_new = tk.Button(btn_frame, text='New Game', width=14)
btn_undo = tk.Button(btn_frame, text='Undo', width=14)
btn_save = tk.Button(btn_frame, text='Save', width=14)
btn_load = tk.Button(btn_frame, text='Load', width=14)
btn_view_db = tk.Button(sidebar, text='View Past Games', width=18)

btn_new.grid(row=0,column=0,padx=3,pady=3)
btn_undo.grid(row=0,column=1,padx=3,pady=3)
btn_save.grid(row=1,column=0,padx=3,pady=3)
btn_load.grid(row=1,column=1,padx=3,pady=3)
btn_view_db.pack(pady=6)

chk = tk.Checkbutton(sidebar, text='Play vs AI', variable=ai_var)
chk.pack(pady=6)

lbl = tk.Label(sidebar, text='AI depth (Minimax)', anchor='w')
lbl.pack(pady=(8,2))
spin = tk.Spinbox(sidebar, from_=1, to=4, width=5, textvariable=depth_var)
spin.pack()

style_frame = tk.LabelFrame(sidebar, text='Piece Style')
style_frame.pack(pady=8, fill='x', padx=6)

style_var = tk.StringVar(value=piece_style)

rb_uni = tk.Radiobutton(style_frame, text='Unicode (classic)', variable=style_var, value='unicode')
rb_min = tk.Radiobutton(style_frame, text='Minimal (circles)', variable=style_var, value='minimal')
rb_hc = tk.Radiobutton(style_frame, text='High-contrast', variable=style_var, value='high_contrast')
rb_uni.pack(anchor='w')
rb_min.pack(anchor='w')
rb_hc.pack(anchor='w')

btn_customize = tk.Button(sidebar, text='Customize Colors', width=18)
btn_customize.pack(pady=6)

# canvas square and piece ids
square_ids = [[None]*8 for _ in range(8)]
piece_ids = {}

# -----------------------
# Helpers & position key
# -----------------------

def position_key():
    rows = []
    for r in range(ROWS):
        row = []
        for c in range(COLS):
            if (r,c) in pieces:
                color, p = pieces[(r,c)]
                row.append(color+p)
            else:
                row.append('..')
        rows.append(''.join(row))
    cp = turn
    cr = ''.join(k[-1] for k,v in castling_rights.items() if v) or '-'
    ep = f"{en_passant[0]}{en_passant[1]}" if en_passant else '-'
    return '|'.join(rows)+f'|{cp}|{cr}|{ep}'

# -----------------------
# Responsive layout
# -----------------------

def recalc_layout(event=None):
    global CELL
    total_w = root.winfo_width() or root.winfo_reqwidth()
    total_h = root.winfo_height() or root.winfo_reqheight()
    sidebar_w = max(220, int(total_w * 0.28))
    board_w = max(200, total_w - sidebar_w - MARGIN)
    avail_h = max(200, total_h - MARGIN)
    CELL = max(28, min(board_w//8, avail_h//8))
    canvas.config(width=CELL*8, height=CELL*8)
    draw_board()

root.bind('<Configure>', recalc_layout)

# -----------------------
# Drawing
# -----------------------

def draw_board():
    canvas.delete('all')
    for r in range(8):
        for c in range(8):
            x1,y1 = c*CELL, r*CELL
            x2,y2 = x1+CELL, y1+CELL
            color = '#F0D9B5' if (r+c)%2==0 else '#B58863'
            square_ids[r][c] = canvas.create_rectangle(x1,y1,x2,y2, fill=color, outline='black')
    draw_pieces()
    highlight_selected_and_moves()

def draw_pieces():
    # delete old piece drawings
    for pid in piece_ids.values():
        # pid may be tuple of ids
        if isinstance(pid, tuple) or isinstance(pid, list):
            for sub in pid:
                canvas.delete(sub)
        else:
            canvas.delete(pid)
    piece_ids.clear()
    style = style_var.get()
    for (r,c),(color,p) in pieces.items():
        x,y = c*CELL+CELL//2, r*CELL+CELL//2
        if style == 'unicode':
            txt = UNICODE.get((color,p), p)
            pid = canvas.create_text(x,y, text=txt, font=('Arial', max(12, int(CELL*0.7))))
            piece_ids[(r,c)] = pid
        elif style == 'minimal':
            # draw a filled circle; outline dark for visibility
            fill = minimal_white_color if color==WHITE else minimal_black_color
            rpad = int(CELL*0.18)
            pid1 = canvas.create_oval(x-CELL//2+rpad, y-CELL//2+rpad, x+CELL//2-rpad, y+CELL//2-rpad, fill=fill, outline='black')
            pid2 = canvas.create_text(x,y, text=p if CELL<36 else '', font=('Arial', max(8, int(CELL*0.3))))
            piece_ids[(r,c)] = (pid1,pid2)
        else:  # high_contrast
            fill = highc_white if color==WHITE else highc_black
            pad = int(CELL*0.12)
            pid1 = canvas.create_rectangle(x-CELL//2+pad, y-CELL//2+pad, x+CELL//2-pad, y+CELL//2-pad, fill=fill, outline='black', width=2)
            pid2 = canvas.create_text(x,y, text=UNICODE.get((color,p),'') if CELL>32 else '', font=('Arial', max(10, int(CELL*0.35))))
            piece_ids[(r,c)] = (pid1,pid2)

# -----------------------
# Game helpers
# -----------------------

def is_in_check(color):
    kr,kc = find_king(color)
    if kr == -1:
        return False
    return is_square_attacked((kr,kc), WHITE if color==BLACK else BLACK, pieces, en_passant, castling_rights)

def highlight_selected_and_moves():
    for r in range(8):
        for c in range(8):
            fill = '#F0D9B5' if (r+c)%2==0 else '#B58863'
            if square_ids[r][c] is not None:
                canvas.itemconfig(square_ids[r][c], fill=fill)
    if selected_sq:
        r,c = selected_sq
        canvas.itemconfig(square_ids[r][c], fill='#7FB3FF')
    for (r,c) in legal_moves_cache:
        canvas.itemconfig(square_ids[r][c], fill='#82E0AA')
    kr,kc = find_king(turn)
    if is_in_check(turn) and 0<=kr<8 and 0<=kc<8:
        canvas.itemconfig(square_ids[kr][kc], fill='#FF6F61')

def update_status():
    turn_label.config(text=f"Turn: {'White' if turn==WHITE else 'Black'}")
    status_label.config(text=f"Halfmove: {halfmove_clock}, Fullmove: {fullmove_number}")

# -----------------------
# Setup & util
# -----------------------

def setup_start_position():
    pieces.clear()
    for c,p in enumerate(PIECE_ORDER):
        pieces[(0,c)] = (BLACK,p)
    for c in range(COLS):
        pieces[(1,c)] = (BLACK,'P')
    for c in range(COLS):
        pieces[(6,c)] = (WHITE,'P')
    for c,p in enumerate(PIECE_ORDER):
        pieces[(7,c)] = (WHITE,p)

def find_king(color):
    for (r,c),(clr,p) in pieces.items():
        if clr==color and p=='K':
            return (r,c)
    return (-1,-1)

# -----------------------
# Move generation (same as before)
# -----------------------

def gen_pseudo_legal_moves_for(square, board, cast_rights_local, en_pass_local):
    if square not in board: return []
    r,c = square
    color, p = board[square]
    moves = []
    opp = WHITE if color==BLACK else BLACK
    if p == 'P':
        direction = -1 if color==WHITE else 1
        f1 = (r+direction, c)
        if 0<=f1[0]<8 and f1 not in board:
            moves.append(f1)
            start_row = 6 if color==WHITE else 1
            f2 = (r+2*direction, c)
            if r==start_row and f2 not in board:
                moves.append(f2)
        for dc in (-1,1):
            cap = (r+direction, c+dc)
            if 0<=cap[0]<8 and 0<=cap[1]<8:
                if cap in board and board[cap][0]==opp:
                    moves.append(cap)
                if en_pass_local and cap == en_pass_local:
                    moves.append(cap)
    elif p == 'N':
        deltas = [(-2,-1),(-2,1),(-1,-2),(-1,2),(1,-2),(1,2),(2,-1),(2,1)]
        for dr,dc in deltas:
            nr,nc = r+dr, c+dc
            if 0<=nr<8 and 0<=nc<8:
                if (nr,nc) not in board or board[(nr,nc)][0]==opp:
                    moves.append((nr,nc))
    elif p in ('B','R','Q'):
        deltas = []
        if p in ('B','Q'):
            deltas += [(-1,-1),(-1,1),(1,-1),(1,1)]
        if p in ('R','Q'):
            deltas += [(-1,0),(1,0),(0,-1),(0,1)]
        for dr,dc in deltas:
            nr,nc = r+dr, c+dc
            while 0<=nr<8 and 0<=nc<8:
                if (nr,nc) not in board:
                    moves.append((nr,nc))
                else:
                    if board[(nr,nc)][0]==opp:
                        moves.append((nr,nc))
                    break
                nr += dr; nc += dc
    elif p == 'K':
        for dr in (-1,0,1):
            for dc in (-1,0,1):
                if dr==0 and dc==0: continue
                nr,nc = r+dr, c+dc
                if 0<=nr<8 and 0<=nc<8:
                    if (nr,nc) not in board or board[(nr,nc)][0]==opp:
                        moves.append((nr,nc))
        row = 7 if color==WHITE else 0
        if (r,c)==(row,4):
            if cast_rights_local.get(f"{color}_K", False):
                if (row,5) not in board and (row,6) not in board:
                    if (row,7) in board and board[(row,7)][0]==color and board[(row,7)][1]=='R':
                        moves.append((row,6))
            if cast_rights_local.get(f"{color}_Q", False):
                if (row,1) not in board and (row,2) not in board and (row,3) not in board:
                    if (row,0) in board and board[(row,0)][0]==color and board[(row,0)][1]=='R':
                        moves.append((row,2))
    return moves

def is_square_attacked(target, by_color, board_local, en_pass_local, cast_rights_local):
    for (r,c),(clr,p) in board_local.items():
        if clr!=by_color: continue
        moves = gen_pseudo_legal_moves_for((r,c), board_local, cast_rights_local, en_pass_local)
        if target in moves:
            return True
    return False

def legal_moves_from(square, board_local, cast_rights_local, en_pass_local):
    if square not in board_local: return []
    color,p = board_local[square]
    moves = gen_pseudo_legal_moves_for(square, board_local, cast_rights_local, en_pass_local)
    legal = []
    for mv in moves:
        new_board = copy.deepcopy(board_local)
        cr = cast_rights_local.copy()
        ep = en_pass_local
        r0,c0 = square
        r1,c1 = mv
        # handle en-passant capture
        if p=='P' and ep and (r1,c1)==ep and c1!=c0 and (r0,c1) in new_board and new_board[(r0,c1)][1]=='P':
            del new_board[(r0,c1)]
        # handle castling rook move
        if p=='K' and abs(c1-c0)==2:
            row = r0
            if c1==6:
                new_board[(row,5)] = new_board.pop((row,7))
            else:
                new_board[(row,3)] = new_board.pop((row,0))
        new_board[(r1,c1)] = new_board.pop((r0,c0))
        kr,kc = (-1,-1)
        for (rr,cc),(clr,t) in new_board.items():
            if clr==color and t=='K':
                kr,kc = rr,cc
                break
        if (kr,kc)==(-1,-1): continue
        if not is_square_attacked((kr,kc), WHITE if color==BLACK else BLACK, new_board, None, cr):
            legal.append(mv)
    return legal

# -----------------------
# Move application & undo
# -----------------------

def push_state_to_history():
    global history, position_counts
    key = position_key()
    position_counts[key] += 1
    history.append((
        copy.deepcopy(pieces),
        turn,
        copy.deepcopy(castling_rights),
        en_passant,
        halfmove_clock,
        fullmove_number,
        key
    ))

def pop_state_from_history():
    global history, pieces, turn, castling_rights, en_passant, halfmove_clock, fullmove_number, position_counts
    if not history: return
    p, t, cr, ep, hm, fm, key = history.pop()
    position_counts[key] -= 1
    pieces.clear()
    pieces.update(p)
    globals()['turn'] = t
    castling_rights.clear(); castling_rights.update(cr)
    globals()['en_passant'] = ep
    globals()['halfmove_clock'] = hm
    globals()['fullmove_number'] = fm

def coord_to_alg(coord):
    r,c = coord
    files = 'abcdefgh'
    ranks = '87654321'
    return f"{files[c]}{ranks[r]}"

def apply_move(src, dst, promotion_choice=None, auto_promote_to='Q'):
    global en_passant, castling_rights, halfmove_clock, fullmove_number, turn, moves_list
    r0,c0 = src; r1,c1 = dst
    mvstr = coord_to_alg(src) + coord_to_alg(dst)
    info = {'src':src,'dst':dst,'captured':None,'promotion':None,'castle':None,'prev_en_pass':en_passant,'prev_castling':castling_rights.copy()}
    color,piece = pieces[src]
    if dst in pieces:
        info['captured'] = pieces[dst]
    if piece=='P' and en_passant and dst==en_passant and c1!=c0 and (r0,c1) in pieces and pieces[(r0,c1)][1]=='P':
        info['captured'] = pieces[(r0,c1)]
        del pieces[(r0,c1)]
    if piece=='K' and abs(c1-c0)==2:
        row = r0
        if c1==6:
            rook_src = (row,7); rook_dst = (row,5)
        else:
            rook_src = (row,0); rook_dst = (row,3)
        info['castle'] = (rook_src,rook_dst, pieces[rook_src])
        pieces[rook_dst] = pieces.pop(rook_src)
    pieces[dst] = pieces.pop(src)
    if piece=='P' and (r1==0 or r1==7):
        if promotion_choice is None:
            if (ai_var.get() and ((play_mode=='human_white' and color==BLACK) or (play_mode=='human_black' and color==WHITE))):
                choice = auto_promote_to
            else:
                choice = simpledialog.askstring("Promotion", "Promote to Q/R/B/N (default Q):", parent=root)
                if not choice: choice = 'Q'
                choice = choice.upper()[0]
                if choice not in ('Q','R','B','N'): choice='Q'
        else:
            choice = promotion_choice
        pieces[dst] = (color, choice)
        info['promotion'] = choice
        mvstr += choice
    moves_list.append(mvstr)
    if piece=='P' and abs(r1-r0)==2:
        globals()['en_passant'] = ((r0+r1)//2,c0)
    else:
        globals()['en_passant'] = None
    if piece=='K':
        castling_rights[f"{color}_K"] = False
        castling_rights[f"{color}_Q"] = False
    if piece=='R':
        if (r0,c0)==(7,0): castling_rights["W_Q"]=False
        if (r0,c0)==(7,7): castling_rights["W_K"]=False
        if (r0,c0)==(0,0): castling_rights["B_Q"]=False
        if (r0,c0)==(0,7): castling_rights["B_K"]=False
    if info['captured']:
        cap_color, cap_piece = info['captured']
        if cap_piece=='R':
            if dst==(7,0): castling_rights["W_Q"]=False
            if dst==(7,7): castling_rights["W_K"]=False
            if dst==(0,0): castling_rights["B_Q"]=False
            if dst==(0,7): castling_rights["B_K"]=False
    if piece=='P' or info['captured']:
        globals()['halfmove_clock'] = 0
    else:
        globals()['halfmove_clock'] += 1
    if color==BLACK:
        globals()['fullmove_number'] += 1
    globals()['turn'] = BLACK if color==WHITE else WHITE
    return info

# -----------------------
# Undo wrapper
# -----------------------

def undo_move():
    global selected_sq, legal_moves_cache, moves_list
    if not history:
        messagebox.showinfo("Undo", "No moves to undo.")
        return
    pop_state_from_history()
    if moves_list:
        moves_list.pop()
    selected_sq = None
    legal_moves_cache = []
    draw_board()
    update_status()

# -----------------------
# Game end checks: checkmate/stalemate, 50-move, threefold
# -----------------------

def game_end_checks():
    key = position_key()
    if position_counts[key] >= 3:
        messagebox.showinfo("Draw", "Threefold repetition — draw.")
        save_game_record(moves_list, 'draw')
        return True
    if halfmove_clock >= 100:
        messagebox.showinfo("Draw", "50-move rule — draw.")
        save_game_record(moves_list, 'draw')
        return True
    for sq,(clr,p) in list(pieces.items()):
        if clr!=turn: continue
        legal = legal_moves_from(sq, pieces, castling_rights, en_passant)
        if legal:
            return False
    king_pos = find_king(turn)
    if is_square_attacked(king_pos, WHITE if turn==BLACK else BLACK, pieces, en_passant, castling_rights):
        winner = 'White' if (WHITE if turn==BLACK else BLACK)==WHITE else 'Black'
        messagebox.showinfo("Checkmate", f"{winner} wins by checkmate.")
        save_game_record(moves_list, winner.lower())
    else:
        messagebox.showinfo("Stalemate", "Stalemate — draw.")
        save_game_record(moves_list, 'draw')
    return True

# -----------------------
# Mouse click handler
# -----------------------

def on_click(evt):
    global selected_sq, legal_moves_cache
    c = int(evt.x // CELL)
    r = int(evt.y // CELL)
    if not (0<=r<8 and 0<=c<8): return
    square = (r,c)
    if selected_sq is None:
        if square in pieces and pieces[square][0]==turn:
            selected_sq = square
            legal_moves_cache = legal_moves_from(square, pieces, castling_rights, en_passant)
            highlight_selected_and_moves()
    else:
        if square in legal_moves_cache:
            push_state_to_history()
            info = apply_move(selected_sq, square)
            key = position_key()
            position_counts[key] += 1
            draw_board()
            update_status()
            finished = game_end_checks()
            selected_sq = None
            legal_moves_cache = []
            draw_board()
            if not finished and ai_var.get():
                if play_mode=='human_white' and turn==BLACK:
                    root.after(50, ai_move)
                elif play_mode=='human_black' and turn==WHITE:
                    root.after(50, ai_move)
        else:
            if square in pieces and pieces[square][0]==turn:
                selected_sq = square
                legal_moves_cache = legal_moves_from(square, pieces, castling_rights, en_passant)
                highlight_selected_and_moves()
            else:
                selected_sq = None
                legal_moves_cache = []
                draw_board()

canvas.bind("<Button-1>", on_click)

# -----------------------
# AI helpers: ordering, simulation
# -----------------------

def move_score(board_local, src, dst):
    score = 0
    if dst in board_local:
        cap = board_local[dst][1]
        score += PIECE_VALUES.get(cap,0) * 10 + 100
    piece = board_local[src][1]
    if piece == 'P' and (dst[0] == 0 or dst[0] == 7):
        score += 500
    rc = dst[0]; cc = dst[1]
    center_pref = 3 - (abs(3.5-rc) + abs(3.5-cc))
    score += center_pref
    return score

def simulate_move_on_board(board_local, cr_local, ep_local, src, dst):
    b2 = copy.deepcopy(board_local)
    cr2 = cr_local.copy()
    ep2 = ep_local
    piece = b2[src][1]
    if piece=='P' and ep2 and dst==ep2 and dst[1]!=src[1]:
        b2.pop((src[0], dst[1]), None)
    if piece=='K' and abs(dst[1]-src[1])==2:
        row = src[0]
        if dst[1]==6:
            b2[(row,5)] = b2.pop((row,7))
        else:
            b2[(row,3)] = b2.pop((row,0))
    b2[dst] = b2.pop(src)
    mover_color = b2[dst][0]
    if piece=='K':
        cr2[f"{mover_color}_K"] = False; cr2[f"{mover_color}_Q"] = False
    if piece=='R':
        if src==(7,0): cr2["W_Q"]=False
        if src==(7,7): cr2["W_K"]=False
        if src==(0,0): cr2["B_Q"]=False
        if src==(0,7): cr2["B_K"]=False
    if piece=='P' and abs(dst[0]-src[0])==2:
        ep_new = ((src[0]+dst[0])//2, src[1])
    else:
        ep_new = None
    return b2, cr2, ep_new

# -----------------------
# Minimax with alpha-beta and transposition table
# -----------------------

def minimax(board_local, cr_local, ep_local, depth, alpha, beta, maximizing):
    key = make_position_key(board_local, WHITE if maximizing else BLACK, cr_local, ep_local)
    tt_key = (key, depth, maximizing)
    if tt_key in transposition_table:
        return transposition_table[tt_key]
    if depth == 0:
        val = evaluate(board_local)
        transposition_table[tt_key] = (val, None)
        return val, None
    color = WHITE if maximizing else BLACK
    moves = generate_all_legal_moves_for(color, board_local, cr_local, ep_local)
    if not moves:
        val = evaluate(board_local)
        transposition_table[tt_key] = (val, None)
        return val, None
    moves.sort(key=lambda mv: move_score(board_local, mv[0], mv[1]), reverse=True)
    best_move = None
    if maximizing:
        max_eval = -math.inf
        for src,dst in moves:
            b2 = copy.deepcopy(board_local)
            cr2 = cr_local.copy()
            ep2 = ep_local
            piece = b2[src][1]
            if piece=='P' and ep2 and dst==ep2 and dst[1]!=src[1]:
                b2.pop((src[0], dst[1]), None)
            if piece=='K' and abs(dst[1]-src[1])==2:
                row = src[0]
                if dst[1]==6:
                    b2[(row,5)] = b2.pop((row,7))
                else:
                    b2[(row,3)] = b2.pop((row,0))
            b2[dst] = b2.pop(src)
            if piece=='K':
                cr2[f"{color}_K"]=False; cr2[f"{color}_Q"]=False
            if piece=='R':
                if src==(7,0): cr2["W_Q"]=False
                if src==(7,7): cr2["W_K"]=False
                if src==(0,0): cr2["B_Q"]=False
                if src==(0,7): cr2["B_K"]=False
            if piece=='P' and abs(dst[0]-src[0])==2:
                ep_new = ((src[0]+dst[0])//2, src[1])
            else:
                ep_new = None
            val, _ = minimax(b2, cr2, ep_new, depth-1, alpha, beta, False)
            if val > max_eval:
                max_eval = val; best_move=(src,dst)
            alpha = max(alpha, val)
            if beta <= alpha:
                break
        transposition_table[tt_key] = (max_eval, best_move)
        return max_eval, best_move
    else:
        min_eval = math.inf
        for src,dst in moves:
            b2 = copy.deepcopy(board_local)
            cr2 = cr_local.copy()
            ep2 = ep_local
            piece = b2[src][1]
            if piece=='P' and ep2 and dst==ep2 and dst[1]!=src[1]:
                b2.pop((src[0], dst[1]), None)
            if piece=='K' and abs(dst[1]-src[1])==2:
                row = src[0]
                if dst[1]==6:
                    b2[(row,5)] = b2.pop((row,7))
                else:
                    b2[(row,3)] = b2.pop((row,0))
            b2[dst] = b2.pop(src)
            if piece=='K':
                cr2[f"{color}_K"]=False; cr2[f"{color}_Q"]=False
            if piece=='R':
                if src==(7,0): cr2["W_Q"]=False
                if src==(7,7): cr2["W_K"]=False
                if src==(0,0): cr2["B_Q"]=False
                if src==(0,7): cr2["B_K"]=False
            if piece=='P' and abs(dst[0]-src[0])==2:
                ep_new = ((src[0]+dst[0])//2, src[1])
            else:
                ep_new = None
            val, _ = minimax(b2, cr2, ep_new, depth-1, alpha, beta, True)
            if val < min_eval:
                min_eval = val; best_move=(src,dst)
            beta = min(beta, val)
            if beta <= alpha:
                break
        transposition_table[tt_key] = (min_eval, best_move)
        return min_eval, best_move

# -----------------------
# Generate all legal moves for color
# -----------------------

def generate_all_legal_moves_for(color, board_local, cr_local, ep_local):
    moves = []
    for sq,(clr,p) in board_local.items():
        if clr!=color: continue
        legal = legal_moves_from(sq, board_local, cr_local, ep_local)
        for dst in legal:
            moves.append((sq,dst))
    return moves

# -----------------------
# Position key for minimax
# -----------------------

def make_position_key(board_local, turn_local, cr_local, ep_local):
    rows = []
    for r in range(ROWS):
        s = []
        for c in range(COLS):
            if (r,c) in board_local:
                clr,p = board_local[(r,c)]
                s.append(clr+p)
            else:
                s.append('..')
        rows.append(''.join(s))
    cr = ''.join(k[-1] for k,v in cr_local.items() if v) or '-'
    ep = f"{ep_local[0]}{ep_local[1]}" if ep_local else '-'
    return '|'.join(rows)+f'|{turn_local}|{cr}|{ep}'

# -----------------------
# Root-level search wrapper for any AI color (FIXED)
# -----------------------

def find_best_move_for(color, depth):
    """Return best (src,dst) for given color with given search depth."""
    transposition_table.clear()
    moves = generate_all_legal_moves_for(color, pieces, castling_rights.copy(), en_passant)
    if not moves:
        return None
    # quick ordering by heuristic
    moves.sort(key=lambda mv: move_score(pieces, mv[0], mv[1]), reverse=True)
    candidates = moves[:ROOT_CANDIDATE_MOVES]
    best_val = math.inf if color==BLACK else -math.inf
    best_move = None
    for src,dst in candidates:
        # simulate root move
        b2 = copy.deepcopy(pieces)
        cr2 = castling_rights.copy()
        ep2 = en_passant
        piece = b2[src][1]
        # handle en-passant capture
        if piece=='P' and ep2 and dst==ep2 and dst[1]!=src[1]:
            b2.pop((src[0], dst[1]), None)
        # handle castling rook movement
        if piece=='K' and abs(dst[1]-src[1])==2:
            row = src[0]
            if dst[1]==6:
                b2[(row,5)] = b2.pop((row,7))
            else:
                b2[(row,3)] = b2.pop((row,0))
        b2[dst] = b2.pop(src)
        # update castling rights for mover
        if piece=='K':
            cr2[f"{color}_K"]=False; cr2[f"{color}_Q"]=False
        if piece=='R':
            if src==(7,0): cr2["W_Q"]=False
            if src==(7,7): cr2["W_K"]=False
            if src==(0,0): cr2["B_Q"]=False
            if src==(0,7): cr2["B_K"]=False
        if piece=='P' and abs(dst[0]-src[0])==2:
            ep_new = ((src[0]+dst[0])//2, src[1])
        else:
            ep_new = None
        # call minimax (note: next ply is opposite color)
        if color==BLACK:
            val, _ = minimax(b2, cr2, ep_new, depth-1, -math.inf, math.inf, True)
            if val < best_val:
                best_val = val; best_move = (src,dst)
        else:
            val, _ = minimax(b2, cr2, ep_new, depth-1, -math.inf, math.inf, False)
            if val > best_val:
                best_val = val; best_move = (src,dst)
    return best_move

# -----------------------
# Evaluate (basic material)
# -----------------------

def evaluate(board_local):
    score = 0
    for (r,c),(clr,p) in board_local.items():
        val = PIECE_VALUES.get(p,0)
        if clr==WHITE:
            score += val
        else:
            score -= val
    return score

# -----------------------
# AI move execution
# -----------------------

def ai_move():
    global turn
    if not ai_var.get(): return
    depth = max(1, depth_var.get())
    ai_color = BLACK if play_mode=='human_white' else WHITE if play_mode=='human_black' else None
    if ai_color is None:
        return
    best = find_best_move_for(ai_color, depth)
    if best is None:
        return
    src,dst = best
    push_state_to_history()
    # AI auto-promotes to queen
    apply_move(src,dst, promotion_choice='Q')
    key = position_key()
    position_counts[key] += 1
    draw_board(); update_status()
    game_end_checks()

# -----------------------
# Save / Load (save to .chess via pickle)
# -----------------------

def save_game():
    fn = filedialog.asksaveasfilename(title="Save game", defaultextension=".chess", filetypes=[("Chess save",".chess"),("All files",".*")])
    if not fn: return
    data = {
        'pieces': pieces,
        'turn': turn,
        'castling_rights': castling_rights,
        'en_passant': en_passant,
        'halfmove_clock': halfmove_clock,
        'fullmove_number': fullmove_number,
        'history': history,
        'position_counts': dict(position_counts),
        'moves_list': moves_list,
        'play_mode': play_mode,
        'piece_style': style_var.get(),
        'minimal_white_color': minimal_white_color,
        'minimal_black_color': minimal_black_color,
        'highc_white': highc_white,
        'highc_black': highc_black
    }
    try:
        with open(fn,'wb') as f:
            pickle.dump(data, f)
        messagebox.showinfo("Save", f"Game saved to {os.path.basename(fn)}")
    except Exception as e:
        messagebox.showerror("Save error", str(e))

def load_game():
    global pieces, turn, castling_rights, en_passant, halfmove_clock, fullmove_number, history, position_counts, selected_sq, legal_moves_cache, play_mode, moves_list, minimal_white_color, minimal_black_color, highc_white, highc_black
    fn = filedialog.askopenfilename(title="Load game", filetypes=[("Chess save",".chess"),("All files",".*")])
    if not fn: return
    try:
        with open(fn,'rb') as f:
            data = pickle.load(f)
        pieces.clear(); pieces.update(data.get('pieces', {}))
        globals()['turn'] = data.get('turn', WHITE)
        castling_rights.clear(); castling_rights.update(data.get('castling_rights', {"W_K":True,"W_Q":True,"B_K":True,"B_Q":True}))
        globals()['en_passant'] = data.get('en_passant', None)
        globals()['halfmove_clock'] = data.get('halfmove_clock', 0)
        globals()['fullmove_number'] = data.get('fullmove_number', 1)
        history = data.get('history', [])
        position_counts.clear(); position_counts.update(data.get('position_counts', {}))
        selected_sq = None; legal_moves_cache = []
        moves_list = data.get('moves_list', [])
        play_mode = data.get('play_mode', 'human_white')
        minimal_white_color = data.get('minimal_white_color', minimal_white_color)
        minimal_black_color = data.get('minimal_black_color', minimal_black_color)
        highc_white = data.get('highc_white', highc_white)
        highc_black = data.get('highc_black', highc_black)
        style_var.set(data.get('piece_style', style_var.get()))
        draw_board(); update_status()
        messagebox.showinfo("Load", f"Game loaded from {os.path.basename(fn)}")
        if ai_var.get() and ((play_mode=='human_white' and turn==BLACK) or (play_mode=='human_black' and turn==WHITE)):
            root.after(50, ai_move)
    except Exception as e:
        messagebox.showerror("Load error", str(e))

# -----------------------
# Start / Initialization
# -----------------------

def start_new_game():
    global pieces, turn, castling_rights, en_passant, halfmove_clock, fullmove_number, history, position_counts, selected_sq, legal_moves_cache, play_mode, moves_list
    pieces.clear()
    castling_rights.clear(); castling_rights.update({"W_K":True,"W_Q":True,"B_K":True,"B_Q":True})
    globals()['turn'] = WHITE
    globals()['en_passant'] = None
    globals()['halfmove_clock'] = 0
    globals()['fullmove_number'] = 1
    history = []
    position_counts.clear()
    selected_sq = None
    legal_moves_cache = []
    moves_list = []
    setup_start_position()
    ans = messagebox.askyesnocancel("Choose side", "Play as White? (Yes=White, No=Black, Cancel=Local 2-player)")
    if ans is True:
        play_mode = 'human_white'
    elif ans is False:
        play_mode = 'human_black'
    else:
        play_mode = 'pvp'
    key = position_key()
    position_counts[key] += 1
    draw_board()
    update_status()
    if ai_var.get() and play_mode=='human_black':
        root.after(100, ai_move)

# -----------------------
# View Past Games popup
# -----------------------

def view_past_games_popup():
    rows = fetch_all_games()
    win = tk.Toplevel(root)
    win.title('Past Games')
    text = tk.Text(win, width=80, height=20)
    text.pack(fill='both', expand=True)
    for row in rows:
        gid, moves, winner, created = row
        text.insert('end', f"ID {gid} | {created} | winner: {winner}\n")
        text.insert('end', f"Moves: {moves}\n\n")
    text.config(state='disabled')

# -----------------------
# Customization dialogs
# -----------------------

def customize_colors():
    global minimal_white_color, minimal_black_color, highc_white, highc_black
    style = style_var.get()
    if style == 'minimal':
        w = colorchooser.askcolor(title='Choose minimal white piece color', color=minimal_white_color)[1]
        if w: minimal_white_color = w
        b = colorchooser.askcolor(title='Choose minimal black piece color', color=minimal_black_color)[1]
        if b: minimal_black_color = b
    elif style == 'high_contrast':
        w = colorchooser.askcolor(title='Choose high-contrast white color', color=highc_white)[1]
        if w: highc_white = w
        b = colorchooser.askcolor(title='Choose high-contrast black color', color=highc_black)[1]
        if b: highc_black = b
    else:
        messagebox.showinfo('Customize', 'Unicode style has no color customization.')
    draw_board()
    # persist
    save_setting('piece_style', style_var.get())
    save_setting('minimal_white_color', minimal_white_color)
    save_setting('minimal_black_color', minimal_black_color)
    save_setting('highc_white', highc_white)
    save_setting('highc_black', highc_black)

# -----------------------
# Wiring UI buttons & startup
# -----------------------
btn_new.config(command=start_new_game)
btn_undo.config(command=undo_move)
btn_save.config(command=save_game)
btn_load.config(command=load_game)
btn_view_db.config(command=view_past_games_popup)
btn_customize.config(command=customize_colors)

# load persisted settings
init_db()
loaded_style = load_setting('piece_style', piece_style)
if loaded_style:
    style_var.set(loaded_style)
minimal_white_color = load_setting('minimal_white_color', minimal_white_color) or minimal_white_color
minimal_black_color = load_setting('minimal_black_color', minimal_black_color) or minimal_black_color
highc_white = load_setting('highc_white', highc_white) or highc_white
highc_black = load_setting('highc_black', highc_black) or highc_black

# start game
start_new_game()
recalc_layout()
update_status()

root.mainloop()
