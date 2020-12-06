args:.Q.def[`name`port!("treetable.q";8888);].Q.opt .z.x

/ remove this line when using in production
/ treetable.q:localhost:8888::
{ if[not x=0; @[x;"\\\\";()]]; value"\\p 8888"; } @[hopen;`:localhost:8888;0];

\l baum.q

(:)c:count first m:1000#'flip cross/[(`a`b`c`d`e`;`f`g`h`i`j`k`l`m`;`n`o`p`q)]
(:)T:([]A:m 0;B:m 1;C:m 2;D:c?.z.D + til 3;E:c?til 6;v:c?1000;w:c#`x`y`z`w)

.baum.tbaum[T;"A,E,D,B,C ~~ counts:count v,v:sum v,w:.baum.nul w"] .baum.open[""] ()

.baum.sort["counts:idesc"] .baum.tbaum[T;"A,E,D,B,C ~~ counts:count v,v:sum v,w:.baum.nul w"] .baum.open[""] ()

.baum.sort["counts:idesc"] .baum.tbaum[T;"A,E,D,B,C ~~ counts:count v,v:sum v,w:.baum.nul w"] .baum.open["A:`a"] ()

.baum.sort["counts:idesc"] .baum.tbaum[T;"A,E,D,B,C ~~ counts:count v,v:sum v,w:.baum.nul w"] .baum.open["A:`a,E:4"] ()

.baum.sort["counts:idesc"] .baum.tbaum[T;"A,E,D,B,C ~~ counts:count v,v:sum v,w:.baum.nul w"] .baum.open["A:`a,E:4"] .baum.open["A:`b"] ()


.baum.tbaum[T;"D,A,E,B,C ~~ counts:count v,v:sum v,w:.baum.nul w"] .baum.open[""] ()

.baum.sort["counts:idesc"] .baum.tbaum[T;"D,A,E,B,C ~~ counts:count v,v:sum v,w:.baum.nul w"] .baum.open[""] ()

.baum.sort["counts:idesc"] .baum.tbaum[T;"D,A,E,B,C ~~ counts:count v,v:sum v,w:.baum.nul w"] .baum.open["D:2020.12.07"] ()

.baum.sort["counts:idesc"] .baum.tbaum[T;"D,A,E,B,C ~~ counts:count v,v:sum v,w:.baum.nul w"] .baum.open["D:2020.12.07,A:`b"] ()


/ 

// example run

/ generate data for the base table t
(:)c:count first m:1000#'flip cross/[(`a`b`c`d`e`;`f`g`h`i`j`k`l`m`;`n`o`p`q)]
(:)T:([]A:m 0;B:m 1;C:m 2;D:c?.z.D + til 3;v:c?1000;w:c#`x`y`z`w)

tbaum[T;"A,D,B,C ~~ counts:count v,v:sum v,w:nul w"] open["A:`,B:2020.12.05"] open["A:`e"] ()

sort["counts:idesc"] tbaum[T;"D,A,B,C ~~ counts:count v,v:sum v,w:nul w"] l:open["D:2020.12.06"] ()

/ dimensions to group on (we can vary the order and number)
G:`A`D`B`C
G:`A`B`C

/ rollups (nul is the default rollup)
A:`counts`v`w!((count;`v);(sum;`v);(nul;`w))

/ initial state
(:)P:([n:enlist(0#`)!0#`]v:enlist 1b)
(:)P:([n:enlist(0#`)!0#0nd]v:enlist 1b)

/ we can drill into T
(:)P1:P                            / initial state
(:)R1:construct[T;G;P1;A]			/ construct root and children 
(:)P2:openat[P1;G;`]              / open at A=a
(:)R2:construct[T;G;P2;A]			/ construct with one node open

tsort[R2;1#`A;1#idesc]



tbaum[T;"A,D,B,C ~~ counts:count v,v:sum v,w:nul w"] open["A:`,B:2020.12.05"] open["A:`e"] ()

sort["counts:iasc"] tbaum[T;"A,D,B,C ~~ counts:count v,v:sum v,w:nul w"] open["A:`"] ()


(:)P3:openat[P2;G;``]			/ open at A=a,B=f
(:)R3:construct[T;G;P3;A]			/ construct with two nodes open
(:)P4:openat[P3;G;`a`f`n]			/ open at A=a,B=f,C=x
(:)R4:construct[T;G;P4;A]			/ construct with two nodes open
(:)P5:closeat[P4;G;`a]             / close at root
(:)R5:construct[T;G;P5;A]			/ R5~R1
(:)P6:openat[P5;G;`a]              / reopen at root
(:)R6:construct[T;G;P6;A]			/ R6~R4

tsort[R4;enlist`v;enlist(iasc)]

/ we can sort a treetable
I:tsort[R6;`w`v;(idesc;iasc)]
R7:1!(0!R6)I

/ we can open T to any level
Q1:opento[T;G;last G]			/ fan open to deepest dimension
S1:construct[T;G;Q1;A]			/ reconstruct with all paths open

/ we can open T to leaves:
Q2:opento[T;G;`]                / open to leaves
S2:construct[T;G;Q2;A]			/ reconstruct with all leaves visible

\

/ recursive tree sort (deprecated)
rsort:{[t;i;c;o]psort[o;value[t][i;c];pfold[k?-1_'k:key[t]`n_;0]]}

/ encode parent vector as nested list of indices
pfold:{[p;i]$[count j:where p=i;i,.z.s[p]each(i=0)_j;i]}

/ sort by fold
psort:{[o;d;q]
 i:1+o d first each 1_q,:();
 first[q],$[type q;q i;raze .z.s[o;d]each q i]}

/

T:("issssffffffsfssf";enlist"\t")0:`:pnl.txt
G:`strategy`unit`trader`symbol

A:`count`qty`volume`trades`pnl`real`unreal`oprice`cprice`vwap!((count;`qty);(sum;`qty);(sum;(abs;`qty));(sum;`trades);(sum;`pnl);(sum;`real);(sum;`unreal);(avg;`oprice);(avg;`cprice);(avg;`vwap))

P:opento[T;G;`trader] 
U:construct[T;G;P;A]

I:tsort[U;0#`;()]
V:1!(0!U)I

\

