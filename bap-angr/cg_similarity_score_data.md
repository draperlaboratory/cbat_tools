# Results

## CG_COMPARE

### Compare the same program compiled with optimization flags 0 and 1

#### BAP

##### Bison

Result:

    1> Total cost: 5466
    1> Total size: 7717.000000
    1> Overall similarity score: 0.291694

Profile sets:

    +----+------------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | Id | Avg time   | Total time | Trials | Avg # Stats | Avg RSS | Avg min RSS | Avg max RSS | Min RSS | Max RSS |
    +----+------------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | 1  | 1181.0847s | 5905.4233s | 5      | 4719        | 743Kb   | 740Kb       | 15182Kb     | 708Kb   | 29668Kb |
    +----+------------+------------+--------+-------------+---------+-------------+-------------+---------+---------+


##### Gawk

Can't get this test to finish. It unexpectedly dies without capturing output.


##### Gnuchess

Result:

    1> Total cost: 0
    1> Total size: 5760.000000
    1> Overall similarity score: 1.000000

Profile stats:

    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | Id | Avg time  | Total time | Trials | Avg # Stats | Avg RSS | Avg min RSS | Avg max RSS | Min RSS | Max RSS |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | 1  | 157.8841s | 789.4205s  | 5      | 630         | 760Kb   | 727Kb       | 20253Kb     | 696Kb   | 28924Kb |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+


##### Grep

Result:

    1> Total cost: 1912
    1> Total size: 3339.000000
    1> Overall similarity score: 0.427373

Profile stats:

    +----+----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | Id | Avg time | Total time | Trials | Avg # Stats | Avg RSS | Avg min RSS | Avg max RSS | Min RSS | Max RSS |
    +----+----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | 1  | 89.0579s | 445.2894s  | 5      | 355         | 778Kb   | 760Kb       | 7184Kb      | 692Kb   | 7832Kb  |
    +----+----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+


##### Gzip

Result:

    1> Total cost: 1564
    1> Total size: 2065.000000
    1> Overall similarity score: 0.242615

Profile stats:

    +----+----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | Id | Avg time | Total time | Trials | Avg # Stats | Avg RSS | Avg min RSS | Avg max RSS | Min RSS | Max RSS |
    +----+----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | 1  | 58.0383s | 290.1915s  | 5      | 231         | 775Kb   | 747Kb       | 7391Kb      | 708Kb   | 19424Kb |
    +----+----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+


##### Less

Result:

    1> Total cost: 1883
    1> Total size: 4142.000000
    1> Overall similarity score: 0.545389

Profile stats:

    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | Id | Avg time  | Total time | Trials | Avg # Stats | Avg RSS | Avg min RSS | Avg max RSS | Min RSS | Max RSS |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | 1  | 112.5077s | 562.5383s  | 5      | 448         | 736Kb   | 582Kb       | 3741Kb      | 4Kb     | 5392Kb  |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+


##### Make

Result:

    1> Total cost: 2746
    1> Total size: 4835.000000
    1> Overall similarity score: 0.432058

Profile stats:

    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | Id | Avg time  | Total time | Trials | Avg # Stats | Avg RSS | Avg min RSS | Avg max RSS | Min RSS | Max RSS |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | 1  | 313.0912s | 1565.4560s | 5      | 1249        | 747Kb   | 736Kb       | 15812Kb     | 696Kb   | 18960Kb |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+


##### Nano

Result:

    1> Total cost: 2584
    1> Total size: 6500.000000
    1> Overall similarity score: 0.602462


Profile stats:

    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | Id | Avg time  | Total time | Trials | Avg # Stats | Avg RSS | Avg min RSS | Avg max RSS | Min RSS | Max RSS |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | 1  | 728.8193s | 3644.0964s | 5      | 2909        | 784Kb   | 782Kb       | 8060Kb      | 692Kb   | 8708Kb  |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+


##### Screen

Result:

    1> Total cost: 3863
    1> Total size: 7466.000000
    1> Overall similarity score: 0.482588

Profile stats:

    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | Id | Avg time  | Total time | Trials | Avg # Stats | Avg RSS | Avg min RSS | Avg max RSS | Min RSS | Max RSS |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | 1  | 698.9245s | 3494.6225s | 5      | 2787        | 752Kb   | 601Kb       | 12980Kb     | 4Kb     | 27200Kb |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+


##### Sed

Result:

    1> Total cost: 1298
    1> Total size: 2320.000000
    1> Overall similarity score: 0.440517

Profile stats:

    +----+----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | Id | Avg time | Total time | Trials | Avg # Stats | Avg RSS | Avg min RSS | Avg max RSS | Min RSS | Max RSS |
    +----+----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | 1  | 27.6390s | 138.1952s  | 5      | 110         | 775Kb   | 740Kb       | 4536Kb      | 696Kb   | 5004Kb  |
    +----+----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+


##### Tar

Can't get this test to finish. It unexpectedly dies without capturing output.


#### ANGR

##### Bison

Result:

    1> # of nodes in call graph 1 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/735211926666/resources/paper_binaries/bison/build.opt0/src/bison): 842
    1> # of edges in call graph 1 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/735211926666/resources/paper_binaries/bison/build.opt0/src/bison): 2182
    1> # of nodes in call graph 2 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/735211926666/resources/paper_binaries/bison/build.opt1/src/bison): 969
    1> # of edges in call graph 2 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/735211926666/resources/paper_binaries/bison/build.opt1/src/bison): 2085
    1> Total size (# of nodes and edges in both call graphs): 6078
    1> Total edit distance: 1241.0
    1> Similarity: 0.795820993748

Profile stats:

    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | Id | Avg time  | Total time | Trials | Avg # Stats | Avg RSS | Avg min RSS | Avg max RSS | Min RSS | Max RSS |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | 1  | 824.2290s | 4121.1449s | 5      | 3293        | 773Kb   | 768Kb       | 16847Kb     | 748Kb   | 20564Kb |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+


##### Gawk

Result:

    1> # of nodes in call graph 1 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/914074830925/resources/paper_binaries/gawk/build.opt0/gawk): 1011
    1> # of edges in call graph 1 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/914074830925/resources/paper_binaries/gawk/build.opt0/gawk): 3309
    1> # of nodes in call graph 2 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/914074830925/resources/paper_binaries/gawk/build.opt1/gawk): 1220
    1> # of edges in call graph 2 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/914074830925/resources/paper_binaries/gawk/build.opt1/gawk): 3121
    1> Total size (# of nodes and edges in both call graphs): 8661
    1> Total edit distance: 2312.0
    1> Similarity: 0.733056229073

Profile stats:

    +----+------------+-------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | Id | Avg time   | Total time  | Trials | Avg # Stats | Avg RSS | Avg min RSS | Avg max RSS | Min RSS | Max RSS |
    +----+------------+-------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | 1  | 2003.6039s | 10018.0196s | 5      | 7999        | 759Kb   | 756Kb       | 25680Kb     | 700Kb   | 33504Kb |
    +----+------------+-------------+--------+-------------+---------+-------------+-------------+---------+---------+


##### Gnuchess

Result:

    1> # of nodes in call graph 1 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/283112933466/resources/paper_binaries/gnuchess/build.opt0/src/gnuchess): 166
    1> # of edges in call graph 1 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/283112933466/resources/paper_binaries/gnuchess/build.opt0/src/gnuchess): 268
    1> # of nodes in call graph 2 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/283112933466/resources/paper_binaries/gnuchess/build.opt1/src/gnuchess): 166
    1> # of edges in call graph 2 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/283112933466/resources/paper_binaries/gnuchess/build.opt1/src/gnuchess): 268
    1> Total size (# of nodes and edges in both call graphs): 868
    1> Total edit distance: 0.0
    1> Similarity: 1.0

Profile stats:

    +----+----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | Id | Avg time | Total time | Trials | Avg # Stats | Avg RSS | Avg min RSS | Avg max RSS | Min RSS | Max RSS |
    +----+----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | 1  | 82.4154s | 412.0772s  | 5      | 329         | 770Kb   | 740Kb       | 10815Kb     | 712Kb   | 15408Kb |
    +----+----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+


##### Grep

Result:

    1> # of nodes in call graph 1 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/891023618880/resources/paper_binaries/grep/build.opt0/src/grep): 518
    1> # of edges in call graph 1 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/891023618880/resources/paper_binaries/grep/build.opt0/src/grep): 1157
    1> # of nodes in call graph 2 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/891023618880/resources/paper_binaries/grep/build.opt1/src/grep): 830
    1> # of edges in call graph 2 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/891023618880/resources/paper_binaries/grep/build.opt1/src/grep): 1497
    1> Total size (# of nodes and edges in both call graphs): 4002
    1> Total edit distance: 1259.0
    1> Similarity: 0.685407296352

Profile stats:

    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | Id | Avg time  | Total time | Trials | Avg # Stats | Avg RSS | Avg min RSS | Avg max RSS | Min RSS | Max RSS |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | 1  | 580.5591s | 2902.7957s | 5      | 2319        | 773Kb   | 770Kb       | 7528Kb      | 708Kb   | 9712Kb  |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+


##### Gzip

Result:

    1> # of nodes in call graph 1 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/802404898963/resources/paper_binaries/gzip/build.opt0/gzip): 264
    1> # of edges in call graph 1 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/802404898963/resources/paper_binaries/gzip/build.opt0/gzip): 488
    1> # of nodes in call graph 2 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/802404898963/resources/paper_binaries/gzip/build.opt1/gzip): 396
    1> # of edges in call graph 2 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/802404898963/resources/paper_binaries/gzip/build.opt1/gzip): 558
    1> Total size (# of nodes and edges in both call graphs): 1706
    1> Total edit distance: 360.0
    1> Similarity: 0.78898007034

Profile stats:

    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | Id | Avg time  | Total time | Trials | Avg # Stats | Avg RSS | Avg min RSS | Avg max RSS | Min RSS | Max RSS |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | 1  | 162.0061s | 810.0304s  | 5      | 647         | 752Kb   | 596Kb       | 6122Kb      | 4Kb     | 11744Kb |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+


##### Less

Error: ANGR has returned this error on me twice:

    2> Traceback (most recent call last):
    2>   File "/home/jqp0205/code/CBAT-internal/code/ANGR/scripts/cg_compare.py", line 338, in <module>
    2>     analysis = ComparisonAnalysis(prj1, prj2)
    2>   File "/home/jqp0205/code/CBAT-internal/code/ANGR/scripts/cg_compare.py", line 245, in __init__
    2>     graph2 = graph_of_prj(prj2)
    2>   File "/home/jqp0205/code/CBAT-internal/code/ANGR/scripts/cg_compare.py", line 231, in graph_of_prj
    2>     def graph_of_prj(prj): return CallGraph(prj)
    2>   File "/home/jqp0205/code/CBAT-internal/code/ANGR/scripts/cg_compare.py", line 20, in __init__
    2>     self.cfg = cfg_of_prj(prj)
    2>   File "/home/jqp0205/code/CBAT-internal/code/ANGR/scripts/cg_compare.py", line 9, in cfg_of_prj
    2>     return prj.analyses.CFGAccurate(normalize=True, context_sensitivity_level=0)
    2>   File "/home/jqp0205/.venvs/cbat/local/lib/python2.7/site-packages/angr/analyses/analysis.py", line 108, in __call__
    2>     oself.__init__(*args, **kwargs)
    2>   File "/home/jqp0205/.venvs/cbat/local/lib/python2.7/site-packages/angr/analyses/cfg/cfg_accurate.py", line 295, in __init__
    2>     self._analyze()
    2>   File "/home/jqp0205/.venvs/cbat/local/lib/python2.7/site-packages/angr/analyses/forward_analysis.py", line 552, in _analyze
    2>     self._analysis_core_baremetal()
    2>   File "/home/jqp0205/.venvs/cbat/local/lib/python2.7/site-packages/angr/analyses/forward_analysis.py", line 677, in _analysis_core_baremetal
    2>     self._process_job_and_get_successors(job_info)
    2>   File "/home/jqp0205/.venvs/cbat/local/lib/python2.7/site-packages/angr/analyses/forward_analysis.py", line 695, in _process_job_and_get_successors
    2>     successors = self._get_successors(job)
    2>   File "/home/jqp0205/.venvs/cbat/local/lib/python2.7/site-packages/angr/analyses/cfg/cfg_accurate.py", line 1284, in _get_successors
    2>     resolved_targets = self._process_one_indirect_jump(ij)
    2>   File "/home/jqp0205/.venvs/cbat/local/lib/python2.7/site-packages/angr/analyses/cfg/cfg_base.py", line 2114, in _process_one_indirect_jump
    2>     resolved, targets = resolver.resolve(self, jump.addr, jump.func_addr, block, jump.jumpkind)
    2>   File "/home/jqp0205/.venvs/cbat/local/lib/python2.7/site-packages/angr/analyses/cfg/indirect_jump_resolvers/jumptable.py", line 69, in resolve
    2>     max_level=3, base_state=self.base_state)
    2>   File "/home/jqp0205/.venvs/cbat/local/lib/python2.7/site-packages/angr/blade.py", line 62, in __init__
    2>     self._backward_slice()
    2>   File "/home/jqp0205/.venvs/cbat/local/lib/python2.7/site-packages/angr/blade.py", line 275, in _backward_slice
    2>     data.get('stmt_idx', None)
    2>   File "/home/jqp0205/.venvs/cbat/local/lib/python2.7/site-packages/angr/blade.py", line 347, in _backward_slice_recursive
    2>     self._backward_slice_recursive(level - 1, pred, regs, stack_offsets, prev, data.get('stmt_idx', None))
    2>   File "/home/jqp0205/.venvs/cbat/local/lib/python2.7/site-packages/angr/blade.py", line 286, in _backward_slice_recursive
    2>     stmts = self._get_irsb(run).statements
    2>   File "/home/jqp0205/.venvs/cbat/local/lib/python2.7/site-packages/angr/blade.py", line 140, in _get_irsb
    2>     irsb = self.project.factory.block(v, backup_state=self._base_state).vex
    2>   File "/home/jqp0205/.venvs/cbat/local/lib/python2.7/site-packages/angr/factory.py", line 288, in block
    2>     strict_block_end=strict_block_end, collect_data_refs=collect_data_refs,
    2>   File "/home/jqp0205/.venvs/cbat/local/lib/python2.7/site-packages/angr/block.py", line 62, in __init__
    2>     collect_data_refs=collect_data_refs,
    2>   File "/home/jqp0205/.venvs/cbat/local/lib/python2.7/site-packages/angr/engines/vex/engine.py", line 519, in lift
    2>     raise SimEngineError("No bytes in memory for block starting at %#x." % addr)
    2> angr.errors.SimEngineError: No bytes in memory for block starting at 0x6877207120726f20.
    [1]
    ==> FAILED (Non-zero exit code)


##### Make

Result:

    1> # of nodes in call graph 1 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/402808666464/resources/paper_binaries/make/build.opt0/make): 507
    1> # of edges in call graph 1 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/402808666464/resources/paper_binaries/make/build.opt0/make): 1673
    1> # of nodes in call graph 2 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/402808666464/resources/paper_binaries/make/build.opt1/make): 630
    1> # of edges in call graph 2 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/402808666464/resources/paper_binaries/make/build.opt1/make): 1626
    1> Total size (# of nodes and edges in both call graphs): 4436
    1> Total edit distance: 972.0
    1> Similarity: 0.78088367899

Profile stats:

    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | Id | Avg time  | Total time | Trials | Avg # Stats | Avg RSS | Avg min RSS | Avg max RSS | Min RSS | Max RSS |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | 1  | 551.8247s | 2759.1233s | 5      | 2202        | 748Kb   | 744Kb       | 10440Kb     | 708Kb   | 13276Kb |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+


##### Nano

Result:

    1> # of nodes in call graph 1 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/885665426760/resources/paper_binaries/nano/build.opt0/src/nano): 624
    1> # of edges in call graph 1 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/885665426760/resources/paper_binaries/nano/build.opt0/src/nano): 1728
    1> # of nodes in call graph 2 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/885665426760/resources/paper_binaries/nano/build.opt1/src/nano): 610
    1> # of edges in call graph 2 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/885665426760/resources/paper_binaries/nano/build.opt1/src/nano): 1656
    1> Total size (# of nodes and edges in both call graphs): 4618
    1> Total edit distance: 595.0
    1> Similarity: 0.871156344738

Profile stats:

    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | Id | Avg time  | Total time | Trials | Avg # Stats | Avg RSS | Avg min RSS | Avg max RSS | Min RSS | Max RSS |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | 1  | 454.0805s | 2270.4027s | 5      | 1811        | 778Kb   | 773Kb       | 10620Kb     | 708Kb   | 14280Kb |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+


##### Screen

Result:

    1> # of nodes in call graph 1 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/010701528305/resources/paper_binaries/screen/build.opt0/screen): 812
    1> # of edges in call graph 1 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/010701528305/resources/paper_binaries/screen/build.opt0/screen): 2505
    1> # of nodes in call graph 2 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/010701528305/resources/paper_binaries/screen/build.opt1/screen): 841
    1> # of edges in call graph 2 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/010701528305/resources/paper_binaries/screen/build.opt1/screen): 1936
    1> Total size (# of nodes and edges in both call graphs): 6094
    1> Total edit distance: 538.0
    1> Similarity: 0.911716442402

Profile stats:

    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | Id | Avg time  | Total time | Trials | Avg # Stats | Avg RSS | Avg min RSS | Avg max RSS | Min RSS | Max RSS |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | 1  | 963.8622s | 4819.3109s | 5      | 3844        | 757Kb   | 755Kb       | 12054Kb     | 696Kb   | 15212Kb |
    +----+-----------+------------+--------+-------------+---------+-------------+-------------+---------+---------+


##### Sed

Can't get this test to finish. It unexpectedly dies without capturing output.


##### Tar

Result:

    1> # of nodes in call graph 1 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/129661569853/resources/paper_binaries/tar/build.opt0/src/tar): 1114
    1> # of edges in call graph 1 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/129661569853/resources/paper_binaries/tar/build.opt0/src/tar): 3466
    1> # of nodes in call graph 2 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/129661569853/resources/paper_binaries/tar/build.opt1/src/tar): 779
    1> # of edges in call graph 2 (of program /home/jqp0205/code/CBAT-internal/.sandbox/builds/129661569853/resources/paper_binaries/tar/build.opt1/src/tar): 1161
    1> Total size (# of nodes and edges in both call graphs): 6520
    1> Total edit distance: 1224.0
    1> Similarity: 0.81226993865

Profile stats:

    +----+------------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | Id | Avg time   | Total time | Trials | Avg # Stats | Avg RSS | Avg min RSS | Avg max RSS | Min RSS | Max RSS |
    +----+------------+------------+--------+-------------+---------+-------------+-------------+---------+---------+
    | 1  | 1320.6252s | 6603.1260s | 5      | 5267        | 771Kb   | 770Kb       | 8139Kb      | 708Kb   | 10048Kb |
    +----+------------+------------+--------+-------------+---------+-------------+-------------+---------+---------+



