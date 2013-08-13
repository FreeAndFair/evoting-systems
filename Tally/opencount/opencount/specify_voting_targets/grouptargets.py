import contests

def do_group_hist(targets, epsilon=2.0):
    """
    Groups a set of voting targets into clusters, which in theory
    should correspond to contests.
    Input: 
        lst targets: Of the form ((x1_i, y1_i, x2_i, y2_i), ...)
    Output:
        lst groups: Of the form (group_i, ...), where each group_i is
        itself a tuple ((x1_i, y1_i, x2_i, y2_i), ...).
    """
    
    def dist(a, b):
        return abs(a[0]-b[0]) + abs(a[1]-b[1])

    if not targets:
        return []
    elif len(targets) == 1:
        return [[targets[0]]]

    close_targets = {}
    for target in targets:
        # Find the closest target
        min_dist = min([dist(target, o) for o in targets if o != target])
        close = [o for o in targets if 0<dist(target,o)<min_dist*(1+epsilon)]
        close_targets[target] = close

    for target,close in close_targets.items():
        close_targets[target] = [x for x in close if target in close_targets[x]]

    return contests.components(close_targets)
