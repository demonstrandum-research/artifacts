#!/usr/bin/env python3
"""Run a python script at IDLE process priority (Windows). Usage: python run_low.py target.py [args...]"""
import ctypes, sys, runpy, os
IDLE_PRIORITY_CLASS = 0x40
ctypes.windll.kernel32.SetPriorityClass(ctypes.windll.kernel32.GetCurrentProcess(), IDLE_PRIORITY_CLASS)
sys.argv = sys.argv[1:]
sys.path.insert(0, os.path.dirname(os.path.abspath(sys.argv[0])))
runpy.run_path(sys.argv[0], run_name="__main__")
