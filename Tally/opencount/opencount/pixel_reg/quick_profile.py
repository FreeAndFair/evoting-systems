import pstats
p=pstats.Stats('dbg.profile')
p.sort_stats('time').print_stats(10)
