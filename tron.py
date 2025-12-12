#!/usr/bin/env python3
import curses, time, random, threading, os

AGENTS = {
    "Beep Boop": {"symbol": "★", "color": 1, "pos": (5,5), "dir": (0,1), "keymap": {"up": "w","down":"s","left":"a","right":"d"}},
    "Harmony": {"symbol": "♬", "color": 2, "pos": (10,10), "dir": (0,-1), "keymap": {"up": "i","down":"k","left":"j","right":"l"}},
    "Chaos": {"symbol": "⚡", "color": 3, "pos": (3,20), "dir": (0,1), "keymap": {"up": "t","down":"g","left":"f","right":"h"}},
    "Flow": {"symbol": "💧", "color": 4, "pos": (15,5), "dir": (0,1), "keymap": {"up": "8","down":"5","left":"4","right":"6"}},
    "Governance": {"symbol": "📜", "color": 5, "pos": (20,15), "dir": (0,1), "keymap": {"up": "u","down":"j","left":"h","right":"k"}}
}

TRAILS = []
DEAD_AGENTS = []
FPS = 5

def faith_meter():
    return "✝️"*random.randint(1,10)

def particle_effect(agent):
    symbols = ["•","★","✨","⚡","💫"]
    return "".join(random.choice(symbols) for _ in range(3))

def input_thread(stdscr):
    while True:
        try: key = stdscr.getkey()
        except: continue
        for agent, props in AGENTS.items():
            km = props["keymap"]
            y, x = props["dir"]
            if key == km.get("up"): props["dir"] = (-1,0)
            if key == km.get("down"): props["dir"] = (1,0)
            if key == km.get("left"): props["dir"] = (0,-1)
            if key == km.get("right"): props["dir"] = (0,1)

def main(stdscr):
    curses.curs_set(0)
    curses.start_color()
    curses.use_default_colors()
    curses.init_pair(1, curses.COLOR_CYAN, -1)
    curses.init_pair(2, curses.COLOR_GREEN, -1)
    curses.init_pair(3, curses.COLOR_RED, -1)
    curses.init_pair(4, curses.COLOR_YELLOW, -1)
    curses.init_pair(5, curses.COLOR_MAGENTA, -1)

    h, w = stdscr.getmaxyx()
    threading.Thread(target=input_thread, args=(stdscr,), daemon=True).start()

    while True:
        stdscr.clear()
        for agent, props in AGENTS.items():
            if agent in DEAD_AGENTS: continue
            y, x = props["pos"]
            dy, dx = props["dir"]
            new_y, new_x = (y+dy)%h, (x+dx)%w
            if any(t[0]==new_y and t[1]==new_x for t in TRAILS):
                DEAD_AGENTS.append(agent)
                continue
            props["pos"] = (new_y, new_x)
            TRAILS.append((new_y,new_x,props["color"],props["symbol"]))

        for y,x,color,sym in TRAILS:
            if 0<=y<h and 0<=x<w-1:
                try: stdscr.addstr(y,x,sym,curses.color_pair(color))
                except: pass

        dashboard_line = " | ".join(
            f"{agent}: {faith_meter()} {particle_effect(agent)}{' (DEAD)' if agent in DEAD_AGENTS else ''}"
            for agent in AGENTS
        )
        try: stdscr.addstr(0,0,dashboard_line[:w-1])
        except: pass

        stdscr.refresh()
        if len(DEAD_AGENTS) == len(AGENTS):
            stdscr.addstr(h//2, w//2-5, "GAME OVER", curses.A_BOLD)
            stdscr.refresh()
            time.sleep(3)
            break
        time.sleep(1/FPS)

if __name__ == "__main__":
    curses.wrapper(main)
