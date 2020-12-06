args:.Q.def[`name`port!("treetable.q";8888);].Q.opt .z.x

/ remove this line when using in production
/ treetable.q:localhost:8888::
{ if[not x=0; @[x;"\\\\";()]]; value"\\p 8888"; } @[hopen;`:localhost:8888;0];

\e 1

/ construct treetable
construct:{[t;g;p;a]r[1#0],g xasc 1_e:(r:root[t;g;a])block[t;g;a]/visible p}


/ visible paths
visible:{[p]
 q:parent n:exec n from p;
 k:(reverse q scan)each til count q;
 n where all each(exec v from p)k}

/ path-list > parent-vector
parent:{[n]n?-1_'n}

/ instruction > constraint
constraint:{[p]flip(in;key p;flip enlist value p)}

/ construct root block
root:{[t;g;a]
 a[g]:nul,'g;
 (`n_,g)xcols node_[`;g]flip enlist each?[t;();();a]}

/ construct a block = node or leaf
block:{[t;g;a;r;p]
 f:$[g~key p;leaf;node g(`,g)?last key p];
 r,(`n_,g)xcols f[t;g;a;p]}

/ construct node block

node:{[b;t;g;a;p]
 c:constraint p;
 a[h]:first,'h:(i:g?b)#g;
 a[h]:{`},'h:(1+i)_g;
 s:?[t;c;enlist[b]!enlist b;a];
 node_[b;g]0!s
 }

/ compute n_ for node block
node_:{[b;g;t]
 num:sum reverse sums reverse b=g;
 f:{x where not null x};
 n:$[count g;num#/:r:flip flip[t]g;enlist til 0];
 if[n~enlist ();n:enlist 0#r . 0 0];
 ![t;();0b;enlist[`n_]!2 enlist/n]
 }

/ construct leaf block
leaf:{[t;g;a;p]
 c:constraint p;
 a:last each a;
 a[g]:g;
 leaf_[g]0!?[t;c;0b;a]}

/ compute n_ for leaf block
leaf_:{[g;t]
 n:flip[flip[t]g],'`$string til count t;
 ![t;();0b;enlist[`n_]!2 enlist/n]}
 
/ keep valid paths
paths:{[p;g]
 n:key each exec n from p;
 i:where til[count g]{(count[y]#x)~y}/:g?/:n;
 1!(0!p)i}

/ open/close to group (h=` > open to leaves)
opento:{[t;g;h]
 k:(1+til count k)#\:k:(g?h)#g;
 n:enlist(0#`)!0#`;
 f:{y,z!/:distinct flip flip[x]z};
 m:distinct n,raze f[t;n]each k;
 ([n:m]v:count[m]#1b)}

/ open/close at a node
at:{[b;p;g;n]p,([n:enlist(count[n]#g)!n,()]v:enlist b)}

openat:at 1b
closeat:at 0b

/ treetable sort
tsort:{[t;c;o]
 n:exec n_ from t;
 i:children[parent n]except enlist();
 j:msort[0!t;c;o]each i;
 n?pmesh over n j}

/ parent-vector > child-list
children:{[p]@[(2+max p)#enlist();first[p],1+1_p;,;til count p]}

/ multi-sort
msort:{[t;c;o;i]i{x y z x}/[til count i;o;flip[t i]c]}

/ mesh nest of paths
pmesh:{i:1+x?-1_first y;(i#x),y,i _ x}

/ predicates (** bugfix 10.18.2015 **)
isopen:{[t;p]key[t][`n_]in value each visible p}
isleaf:{[t;g]count[g]=level t}

/ level of each record
level:{[t]count each key[t]`n_}

/ first if 1=count else null (for syms, non-summable nums)
nul:{first$[1=count distinct x,();x;0#x]}

/ discard invalid paths
valid:{[p;g]
 n:key each exec n from p;
 i:where til[count g]{(count[y]#x)~y}/:g?/:n;
 1!(0!p)i}

// parallel variant

/ construct treetable (parallel)
pconstruct:{[t;g;p;a]1!`n_ xasc root[t;g;a],raze pblock[t;g;a]peach visible p}

/ construct a block (parallel)
pblock:{[t;g;a;p]
 f:$[g~key p;leaf;node g(`,g)?last key p];
 (`n_,g)xcols f[t;g;a;p]}

// example run

/ generate data for the base table t
(:)c:count first m:1000#'flip cross/[(`a`b`c`d`e`;`f`g`h`i`j`k`l`m`;`n`o`p`q)]
(:)T:([]A:m 0;B:m 1;C:m 2;D:c?.z.D + til 3;v:c?1000;w:c#`x`y`z`w)
T
/ dimensions to group on (we can vary the order and number)
G:`D`A`B`C
G:`A`B`C

/ rollups (nul is the default rollup)
A:`counts`v`w!((count;`v);(sum;`v);(nul;`w))

/ initial state
(:)P:([n:enlist(0#`)!0#`]v:enlist 1b)
(:)P:([n:enlist(0#`)!0#0nd]v:enlist 1b)

/ we can drill into T
(:)P1:P                            / initial state
(:)R1:construct[T;G;P1;A]			/ construct root and children 
(:)P2:openat[P1;G;2020.12.05]              / open at A=a
(:)R2:construct[T;G;P2;A]			/ construct with one node open

tsort[R2;1#`counts;1#idesc]




I:tsort[R2;1#`counts;1#idesc]
1!(0!R2)I

`t`c`o set' (R2;1#`counts;1#idesc)

(0!t) 3 4 0 1 2 5 6 7 8 9

tsort:{[t;c;o]
 n:exec n_ from t;
 i:children[parent n]except enlist();
 j:msort[0!t;c;o]each i;
 I:n?pmesh over n j;
 1!(0!t)I
 }

tsort[1!(0!t) 3 4 0 1 2 5 6 7 8 9;1#`counts;1#idesc]

parent:{[n]
 n?-1_'n
 }

([]num:til count n;n;p:parent n)




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

