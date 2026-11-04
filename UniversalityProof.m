
(*Master file for the proof*)
ClearAll["Global`*"];

(***************basic definitions****************************)
(*This is square distance*)
Distance2[V_,W_]:=Dot[V-W,V-W];

(*volume*)
Vol[A0_,A1_,A2_,A3_] :=  Det[{A0-A3,A1-A3,A2-A3}];

(*This switches the sign of a polynomial if it is negative at (1/2,1/2)*)
MakePositive[poly_] := Module[{q, test},
  q = Expand[poly];
  test = q /. {t -> 1/2, h -> 1/2};
  If[test < 0, q = -q];
  Return[q];
];

(*Triangle list*)

tri = {
    {0,1,2},{0,3,1},{0,2,4},{0,4,3},{1,5,2},{1,3,6},{1,4,5},{1,7,4},
    {1,6,7},{2,6,4},{2,5,7},{2,7,6},{3,4,7},{3,5,6},{3,7,5},{4,6,5}
};

(*Edge list*)

edge = {
{0,1},{0,2},{0,3},{0,4},{1,2},{1,3},{1,4},{1,5},{1,6},{1,7},{2,4},{2,5},
{2,6},{2,7},{3,4},{3,5},{3,6},{3,7},{4,5},{4,6},{4,7},{5,6},{5,7},{6,7}
};

(* All increasing quadruples *)
QLIST = Subsets[Range[8], {4}];



(******************done with basic definitions**********************)

(********************the families of origami tori*******************)
(* The general 5-parameter family *)


main[x_, y_, u_, k_, lambda_] := Module[{b, a, p},

  b = 1 - x - 2*k;
  a = u - x - k + 1/2;

  p = {
    {0, 0, 0},
    {2*u*y, 2*u*(b + 2*k/lambda), 0},
    {(2*u - 1)*y, (1 - 2*u)*x, 0},
    {-2*y*(k + b*lambda), lambda*(y*y - b*b) - 2*b*k, 0},
    {(2*x + 2*k - 1)*y, y*y + b*x, 0},
    {(2*u - 1)*y, y*y + b*(b + 2*u - 1), 0},
    {2*y*(u - k), 2*b*(u - k), 0},
    {2*u*y, y*y + b*b + 2*b*u - 2*a/(1 - lambda), 0}
  };

  p/(2*y)
];

(* Left special family. The last 3 parameters of main are u,k,lambda - as in the paper*)

good1[x_, y_] := Module[{p},
  p = main[x, y, 3/128, 11/32, 13/32];
  p[[All, 3]] = {0, 0, -2, 3, 1, -2, 2, 1024+1024 y y};
  p
];

(* right special family. The last 3 parameters of main are u,k,lambda - as in the paper*)

good2[x_, y_] := Module[{p},
  p = main[x, y, x/2 - 1/2048, 1/16, 1/2];
  p[[All, 3]] = {0, 0, -4, -2, 2048, -4, 1816*x - 229, 16384+16384 y y};
  p
];

(*Now we define 2 smaller families, defined on the infinite halfstrip Omega
using the parametrizations descibed in Ch 5.  This parametrization lets us
do the strip dom tests in a uniformw way.*)

(* These are the reparametrized families so that the
domain is the half-strip Omega. The constants are in the paper.
We are covering a superset of our domains.*)

 good1A[t0_,h_] := Module[{t,x,y},
    t= (43/512)*t0;
    x=2*t/(t*t+1);
    y=(1-t*t)/(t*t+1)+h;
    good1[x,y]
];

good2A[t0_,h_] := Module[{t,x,y},
    t=(9/128)*(1-t0)+(9/32)*t0;
    x=2*t/(t*t+1);
    y=(1-t*t)/(t*t+1)+h;
    good2[x,y]
];

u[t_]:=2 t/(1+t t)
Print["setting u[t_]:=2 t/(1+t t) we first compute that these are positive:"];
Print["u[43/512]-1/6: ",u[43/512]-1/6];
Print["u[144/512]-1/2: ",u[144/512]-1/2];
Print["this makes sure we have covered our intervals"];


(*************Done defining the families**************)

(**************Strip dominance************************************)

PartialSum[X_]:=Table[Sum[X[[j]],{j,1,k}],{k,1,Length[X]}];
Posdom1Variable[P_,t_]:=Min[Sign[PartialSum[CoefficientList[P,t]]]];

StripDomPoly[P_] := Module[{CO,A,B1,B2,B3},
  CO = CoefficientList[Expand[P],h];
  A = Posdom1Variable[CO[[1]],t];
  B1 = Table[Posdom1Variable[CO[[j]],t],{j,1,Length[CO]}];
  B2 = Min[B1];
  B3 = If[B2>=0,1,0];
  Min[A,B3]
];

(*We test both the numerator and denominator*)

StripDom[P_]:=Module[{num,den},
num=StripDomPoly[MakePositive[Numerator[Factor[P]]]];
den=StripDomPoly[MakePositive[Denominator[Factor[P]]]];
Min[num,den]]

(************done with dominance definitions**************)

(*************This is the flatness check*********************)
(*Note: I set lambda=l*)

(*Origami torus points*)
MainFamilyReloaded = main[x,y,u,k,l];
PP = Table[Take[MainFamilyReloaded[[i]],2],{i,1,8}];

(* Flat torus points: only the 4th and 7th points differ.
Here we mean to count from 1. In the paper these are w3 and w6*)

WW = PP;
WW[[4]] = { k, -(2*k*(1-x-2*k)+l*((1-x-2*k)^2+y^2))/(2*y)};
WW[[7]] = { u+k, (1-x-2*k)*(u-k)/y};

(*Getting a point that is translated by a lattice.
 lattice is Lambda(x,y). The translate is a(1,0) + b(x,y)*)

point[k_,a_,b_] := WW[[k+1]] + {a+b*x,b*y};

(*Here is the list of 16 fundamental triangles for the flat torus*)

triangles[] := Module[{w0,w1,w2,w3,w4,w5,w6,w7, w2e,w3t,w4t,w4et,w5e,w5et},
w0=WW[[1]];
w1=WW[[2]];
w2=WW[[3]];
w3=WW[[4]];
w4=WW[[5]];
w5=WW[[6]];
w6=WW[[7]];
w7=WW[[8]];
w2e=point[2,1,0];
w3t=point[3,0,1];
w4t=point[4,0,-1];
w4et=point[4,1,-1];
w5e=point[5,1,0];
w5et=point[5,1,-1];

{
{w0,w1,w2},       (* 012 *)
{w0,w3,w1},       (* 031 *)
{w0,w2,w4t},      (* 024 *)
{w0,w4t,w3},      (* 043 *)
{w1,w5,w2},       (* 152 *)
{w1,w3,w6},       (* 136 *)
{w1,w4,w5},       (* 145 *)
{w1,w7,w4},       (* 174 *)
{w1,w6,w7},       (* 167 *)
{w2e,w6,w4et},    (* 264 *)
{w2e,w5e,w7},     (* 257 *)
{w2e,w7,w6},      (* 276 *)
{w3t,w4,w7},      (* 347 *)
{w3,w5et,w6},     (* 356 *)
{w3t,w7,w5e},     (* 375 *)
{w4et,w6,w5et}    (* 465 *)
}
];

(* Here is the distance check *)
CheckIsometry[i_] := Module[{a, b},
  a = triangles[][[i]];
  b = PP[[tri[[i]] + 1]];
  Simplify[{
    Distance2[a[[1]], a[[2]]] - Distance2[b[[1]], b[[2]]],
    Distance2[a[[1]], a[[3]]] - Distance2[b[[1]], b[[3]]],
    Distance2[a[[2]], a[[3]]] - Distance2[b[[2]], b[[3]]]
  }]
];

Print["******* FLATNESS CHECK***********"];
Print["should be all 0"];
Print[Table[CheckIsometry[ii],{ii,1,16}]]

(*****************************************)
(*This tests the nondegeneracy of the triangles*)

TriArea[P_, TRI_] := Module[{W1, W2, W3},
  W1 = Take[P[[TRI[[1]] + 1]], 2];
  W2 = Take[P[[TRI[[2]] + 1]], 2];
  W3 = Take[P[[TRI[[3]] + 1]], 2];
  Det[{W1-W3, W2-W3}]
];

AREA1A[t_, h_, k_] := TriArea[good1A[t, h], tri[[k]]];
AREA2A[t_, h_, k_] := TriArea[good2A[t, h], tri[[k]]];
areaList1A=Table[AREA1A[t,h,k],{k,1,16}];
areaList2A=Table[AREA2A[t,h,k],{k,1,16}];
areaPos1A=Table[StripDom[areaList1A[[j]]],{j,1,16}];
areaPos2A=Table[StripDom[areaList2A[[j]]],{j,1,16}];

Print["********************************"];
Print["******* NONDEGENERACY CHECK***********"];
Print["return of 1 means num and den are strip dominant"];
Print["areaList 1A: ",areaPos1A];
Print["areaList 2A: ",areaPos2A];

(*************************lifting test******************)
(*Now we are taking the volumes. strip dom for numerator and denominator*)

VOL1A[t_, h_, QUAD_] := Module[{P},
  P = good1A[t, h];
  Vol[P[[QUAD[[1]]]], P[[QUAD[[2]]]], P[[QUAD[[3]]]], P[[QUAD[[4]]]]]
];

VOL2A[t_, h_, QUAD_] := Module[{P},
  P = good2A[t, h];
  Vol[P[[QUAD[[1]]]], P[[QUAD[[2]]]], P[[QUAD[[3]]]], P[[QUAD[[4]]]]]
];

(* Compute the volumes *)
list1A = Table[VOL1A[t,h,Q], {Q,QLIST}];
list2A = Table[VOL2A[t,h,Q], {Q,QLIST}];

(* Test the volumes *)
pos1A = Table[StripDom[P], {P,list1A}];
pos2A = Table[StripDom[P], {P,list2A}];

Print["********************************"];
Print["******* LIFTING CHECK *********"];
Print["Return of 1 means num and den are strip dominant"];

Print["list 1A: ",pos1A];
 
(*prints out any failures*)
Do[If[pos1A[[i]] != 1, Print[i, ": ", QLIST[[i]]-1]], {i,1,70}];

Print["list 2A: ",pos2A];

(*prints out any failures*)
Do[If[pos2A[[i]] != 1, Print[i, ": ", QLIST[[i]]-1]], {i,1,70}];

(*******************transversality check******************)
Print["*****************************************************************"];
Print["******* TRANSVERSALITY CHECK (ABOUT 15 SEC)***********"];

(*list of point variables*)
V = {{x0,y0},{x1,y1},{x2,y2},{x3,y3}, {x4,y4},{x5,y5},{x6,y6},{x7,y7}};

(* The orientation signs of the 16 triangles: +1 is counterclockwise. *)
sgn = {1,-1,-1,1,1,1,1,1,-1,1,-1,-1,-1,-1,1,-1};

(* Gets the position of vertex v in TRI, or 0 if absent. *)

vertexPosition[TRI_,v_] :=
  Total[Flatten[Position[TRI,v]]];

(* Purely combinatorial helper routine. *)

angleSigns[TRI_,m_] := Module[{L,p},
  L={{0,0},{-1,-1},{1,0},{0,1}};
  p=vertexPosition[TRI,m];
  L[[p+1]]
];

(* Computes the derivative of the angle at the first vertex
of TRI with respect to the X-coord of V[[m+1]].  Our paper counts from 0
and Mathematica counts from 1. That is why we have m+1*)

firstVertexDiffX[TRI_,m_,sign_] := Module[{u,w,as,e1,e2},
  u=V[[TRI[[2]]+1]]-V[[TRI[[1]]+1]];
  w=V[[TRI[[3]]+1]]-V[[TRI[[1]]+1]];
  as=angleSigns[TRI,m];
  e1=+as[[1]] u[[2]]/Dot[u,u];
  e2=-as[[2]] w[[2]]/Dot[w,w];
  sign*(e1+e2)
];

(* Computes the derivative of the angle at vertex v in TRI.
Rotates TRI so that v comes first. Returns 0 if v is absent. *)

anyVertexDiffX[TRI_,v_,m_,sign_] := Module[{p,A},
  p=vertexPosition[TRI,v];
  A=RotateLeft[TRI,p-1];
  Min[p,1] firstVertexDiffX[A,m,sign]
];

(*Sums over the 16 contributing triangles. Some contributions are 0*)

ConeAngleDiffX[v_,m_] := Total[Table[anyVertexDiffX[tri[[i]],v,m,sgn[[i]]],{i,1,16}]];

(*The 7 x 7 Jacobian of the first 7 cone angles
with respect to the first 7 x coordinates.*)

JAC=Table[ConeAngleDiffX[k,m],{k,0,6},{m,0,6}];

(*This gets our points into the form where you can
substitute these for the general variables*)

points1A = good1A[t,h];
fam1A = {};
Do[AppendTo[fam1A, V[[ii,1]] -> points1A[[ii,1]]];
AppendTo[fam1A, V[[ii,2]] -> points1A[[ii,2]]];,{ii,1,8}];

points2A = good2A[t,h];
fam2A = {};
Do[AppendTo[fam2A, V[[ii,1]] -> points2A[[ii,1]]];
AppendTo[fam2A, V[[ii,2]] -> points2A[[ii,2]]];,{ii,1,8}];

fam1A=FullSimplify[fam1A];
fam2A=FullSimplify[fam2A];

JAC1A = JAC /.fam1A;
JAC2A = JAC /.fam2A;

P1A=Det[JAC1A];
P2A=Det[JAC2A];

P1A1=P1A/.t->t/2;
P1A2=P1A/.t->1-t/2;
P2A1=P2A/.t->t/2;
P2A2=P2A/.t->1-t/2;

Print["strip dom tweak for P1A1: ",StripDom[P1A1]];
Print["strip dom tweak for P1A2: ",StripDom[P1A2]];
Print["strip dom tweak for P2A1: ",StripDom[P2A1]];
Print["strip dom tweak for P2A2: ",StripDom[P2A2]];

(**********************embedding check*********************)

(*returns 5 if and only if edge e is disjoint from triangle d.
  We automatically pass pairs which do not have this disjointness*)
  
goodPair[e_,d_]:=Length[Union[Flatten[{e,d}]]];

(*list of all edge-triangle pairs*)
BIG=Table[Table[{edge[[j]],tri[[i]]},{j,1,Length[edge]}],{i,1,Length[tri]}];
BIG=Flatten[BIG,1];

(*Returns 0 if the segment and triangle are disjoint, or irrelevant.
We want this test to be 0 384 times.*)

segTriTest[PP0_,e_,f_] := Module[{E0,E1,X0,X1,X2,v0,v1,v2,v3,v4,test1,test2,test3,test4,test},

    E0=PP0[[e[[1]]+1]];
    E1=PP0[[e[[2]]+1]];
    X0=PP0[[f[[1]]+1]];
    X1=PP0[[f[[2]]+1]];
    X2=PP0[[f[[3]]+1]];

    v0=Vol[E1,X0,X1,X2];
    v1=Vol[E0,X0,X1,X2];
    v2=Vol[E0,E1,X1,X2];
    v3=Vol[E0,E1,X0,X2];
    v4=Vol[E0,E1,X0,X1];

    test1=If[v0 v1>0,1,0];
    test2=If[v2 v3>0,1,0];
    test3=If[v3 v4>0,1,0];
    test4=If[goodPair[e,f]<5,1,0];

    test=test1+test2+test3+test4;
    If[test==0,1,0]
];

(*The embedding test: should be 0. We are adding
0 or 1 a total of 384 times, and we want all 0s*)

embeddingTest[PP0_] := Sum[segTriTest[PP0,BIG[[i,1]],BIG[[i,2]]], {i,1,Length[BIG]}];

Print["*********************************"];
Print["******* EMBEDDING CHECK AT (0,1) for first family and (8/17,1) for the second *****"];
Print["0 means embedded"];
Print["Embedding test 1: ",embeddingTest[good1[0,1]]];
Print["Embedding test 2: ",embeddingTest[good2[8/17,1]]];
Print["********************************"];
Print["ALL DONE"];
