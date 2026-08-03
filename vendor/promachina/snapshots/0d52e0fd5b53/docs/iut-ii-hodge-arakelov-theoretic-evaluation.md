¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II:
HODGE-ARAKELOV-THEORETIC EVALUATION
Shinichi Mochizuki
December 2020
Abstract. In the present paper, which is the second in a series of four pa-
pers, westudytheKummer theory surroundingtheHodge-Arakelov-theoreticeval-
uation — i.e., evaluation in the style of the scheme-theoretic Hodge-Arakelov
theory established by the author in previous papers — of the [reciprocal of the l-
th root of the] theta function at l-torsion points [strictly speaking, shifted by a
suitable 2-torsion point], for l ≥ 5 a prime number. In the first paper of the series, we
studied “miniature models of conventional scheme theory”, which we referred to as
Θ±ellNF-Hodge theaters, that were associated to certain data, called initial Θ-data,
that includes an elliptic curve EF over a number field F , together with a prime num-
ber l ≥ 5. The underlying Θ-Hodge theaters of these Θ±ellNF-Hodge theaters were
glued to one another by means of“Θ-links”, that identify the [reciprocal of the l-th
root of the] theta function at primes of bad reduction of EF in one Θ±ellNF-Hodge
theater with [2l-th roots of] the q-parameter at primes of bad reduction of EF in an-
other Θ±ellNF-Hodge theater. The theory developed in the present paper allows one
to construct certain new versions of this “Θ-link”. One such new version is the Θ×μ
gau-
link, which is similar to the Θ-link, but involves the theta values at l-torsion points,
rather than the theta function itself. One important aspect of the constructions
that underlie the Θ×μ
gau-link is the study of multiradiality properties, i.e., properties
of the “arithmetic holomorphic structure” — or, more concretely, the ring/scheme
structure — arising from one Θ±ellNF-Hodge theater that may be formulated in
such a way as to make sense from the point of the arithmetic holomorphic structure
of another Θ±ellNF-Hodge theater which is related to the original Θ±ellNF-Hodge
theater by means of the [non-scheme-theoretic!] Θ×μ
gau-link. For instance, certain of
the various rigidity properties of the´ etale theta function studied in an earlier paper
by the author may be intepreted as multiradiality properties in the context of the
theory of the present series of papers. Another important aspect of the constructions
that underlie the Θ×μ
gau-link is the study of “conjugate synchronization” via the
F ±
l -symmetry of a Θ±ellNF-Hodge theater. Conjugate synchronization refers to a
certain system of isomorphisms — which are free of any conjugacy indeterminacies!
— between copies of local absolute Galois groups at the various l-torsion points at
which the theta function is evaluated. Conjugate synchronization plays an impor-
tant role in the Kummer theory surrounding the evaluation of the theta function at
l-torsion points and is applied in the study of coricity properties of [i.e., the study of
objects left invariant by] the Θ×μ
gau-link. Global aspects of conjugate synchronization
require the resolution, via results obtained in the first paper of the series, of certain
technicalities involving profinite conjugates of tempered cuspidal inertia groups.
Typeset by AMS-TEX
1
2 SHINICHI MOCHIZUKI
Contents:
Introduction
§1. Multiradial Mono-theta Environments
§2. Galois-theoretic Theta Evaluation
§3. Tempered Gaussian Frobenioids
§4. Global Gaussian Frobenioids
Introduction
1
In the following discussion, we shall continue to use the notation of the In-
troduction to the first paper of the present series of papers [cf. [IUTchI], §I1]. In
particular, we assume that are given an elliptic curve EF over a number field F,
together with a prime number l ≥ 5. In the present paper, which forms the sec-
ond paper of the series, we study the Kummer theory surrounding the Hodge-
Arakelov-theoretic evaluation [cf. Fig. I.1 below] — i.e., evaluation in the
style of the scheme-theoretic Hodge-Arakelov theory of [HASurI], [HASurII] — of
the reciprocal of the l-th root of the theta function
Θ
v
def
= √−1·
1
2(m+1
2)2
q
v
−1
m∈Z
·
n∈Z
(−1)n
1
2(n+1
2)2
·q
v·Un+1
2
v
−
l
[cf. [EtTh], Proposition 1.4; [IUTchI], Example 3.2, (ii)] at l-torsion points
[strictly speaking, shifted by a suitable 2-torsion point] in the context of the theory
of Θ±ellNF-Hodge theaters developed in [IUTchI]. Here, relative to the notation
of [IUTchI], §I1, v ∈ Vbad
; qv denotes the q-parameter at v of the given elliptic
curve EF over a number field F; Uv denotes the standard multiplicative coordinate
on the Tate curve obtained by localizing EF at v. Let q
be a 2l-th root of qv.
v
Then these “theta values at l-torsion points” will, up to a factor given by a 2l-th
root of unity, turn out to be of the form [cf. Remark 2.5.1, (i)]
j2
q
v
[Frobenius-like!]
Frobenioid-theoretic
theta function
Kummer
.........
[´ etale-like!]
Galois-theoretic ´ etale
theta function
evalu- ⇓ ation evalu- ⇓ ation
[Frobenius-like!]
Frobenioid-theoretic
theta values
Kummer
.........
[´ etale-like!]
Galois-theoretic
theta values
Fig. I.1: The Kummer theory surrounding Hodge-Arakelov-theoretic evaluation
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 3
— where j ∈ {0,1,...,l def = (l−1)/2}, so j is uniquely determined by its image
j ∈ |Fl| def
= Fl/{±1}= {0} Fl [cf. the notation of [IUTchI], §I1].
In order to understand the significance of Kummer theory in the context
of Hodge-Arakelov-theoretic evaluation, it is important to recall the notions of
“Frobenius-like” and “´ etale-like” mathematical structures [cf. the discussion of
[IUTchI], §I1]. In the present series of papers, the Frobenius-like structures consti-
tuted by [the monoidal portions of] Frobenioids — i.e., more concretely, by various
monoids — play the important role of allowing one to construct gluing isomor-
phisms such as the Θ-link which lie outside the framework of conventional
scheme/ring theory [cf. the discussion of [IUTchI], §I2]. Such gluing isomor-
phisms give rise to Frobenius-pictures [cf. the discussion of [IUTchI], §I1]. On
the other hand, the ´ etale-like structures constituted by various Galois and arith-
metic fundamental groups give rise to the canonical splittings of such Frobenius-
pictures furnished by corresponding´ etale-pictures [cf. the discussion of [IUTchI],
§I1]. In [IUTchIII], absolute anabelian geometry will be applied to these Galois
and arithmetic fundamental groups to obtain descriptions of alien arithmetic
holomorphic structures, i.e., arithmetic holomorphic structures that lie on the
opposite side of a Θ-link from a given arithmetic holomorphic structure [cf. the
discussion of [IUTchI], §I3]. Thus, in light of the equally crucial but substantially
diﬀerent roles played by Frobenius-like and´ etale-like structures in the present series
of papers, it is of crucial importance to be able
to relate corresponding Frobenius-like and´ etale-like versions of vari-
ous objects to one another.
This is the role played by Kummer theory. In particular, in the present paper,
we shall study in detail the Kummer theory that relates Frobenius-like and ´ etale-
like versions of the theta function and its theta values at l-torsion points to one
another [cf. Fig. I.1].
One important notion in the theory of the present paper is the notion of mul-
tiradiality. To understand this notion, let us recall the´ etale-picture discussed
in [IUTchI], §I1 [cf. [IUTchI], Fig. I1.6]. In the context of the present paper, we
shall be especially interested in the´ etale-like version of the theta function and its
theta values constructed in each D-Θ±ellNF-Hodge theater (−)HT D-Θ±ellNF; thus,
one can think of the ´ etale-picture under consideration as consisting of the diagram
given in Fig. I.2 below. As discussed earlier, we shall ultimately be interested in
applying various absolute anabelian reconstruction algorithms to the various arith-
metic fundamental groups that [implicitly] appear in such ´ etale-pictures in order
to obtain descriptions of alien holomorphic structures, i.e., descriptions of objects
that arise on one “spoke” [i.e., “arrow emanating from the core”] that make sense
from the point of view of another spoke. In this context, it is natural to classify the
various algorithms applied to the arithmetic fundamental groups lying in a given
spoke as follows [cf. Example 1.7]:
· We shall refer to an algorithm as coric if it in fact only depends on
input data arising from the mono-analytic core of the ´ etale-picture, i.e.,
the data that is common to all spokes.
4 SHINICHI MOCHIZUKI
· We shall refer to an algorithm as uniradial if it expresses the objects
constructed from the given spoke in terms that only make sense within
the given spoke.
· We shall refer to an algorithm as multiradial if it expresses the objects
constructed from the given spoke in terms of corically constructed objects,
i.e., objects that make sense from the point of view of other spokes.
Thus, multiradial algorithms are compatible with simultaneous execution at
multiple spokes[cf. Example1.7, (v); Remark1.9.1], whileuniradialalgorithmsmay
only be consistently executed at a single spoke. Ultimately, in the present series of
papers, we shall be interested — relative to the goal of obtaining “descriptions of
alien holomorphic structures” — in the establishment of multiradial algorithms for
constructing the objects of interest, e.g., [in the context of the present paper] the
´ etale-like versions of the theta functions and the corresponding theta values
discussed above. Typically, in order to obtain such multiradial algorithms, i.e.,
algorithms that make sense from the point of view of other spokes, it is necessary
to allow for some sort of “indeterminacy” in the descriptions that appear in the
algorithms of the objects constructed from the given spoke.
´ etale-like version of
j2
Θ
v, {q
}
v
...
|...
´ etale-like version of
j2
Θ
v, {q
}
v
— (−)D⊢
>
—
´ etale-like version of
j2
Θ
v, {q
}
v
|
...
...
´ etale-like version of
j2
Θ
v, {q
}
v
Fig. I.2:
´
Etale-picture of ´ etale-like versions of theta functions, theta values
Relative to the analogy between the inter-universal Teichm¨ uller theory of the
present series of papers and the classical theory of holomorphic structures on
Riemann surfaces [cf. the discussion of [IUTchI], §I4], one may think of coric
algorithms as corresponding to constructions that depend only on the underlying
real analytic structure on the Riemann surface. Then uniradial algorithms cor-
respond to constructions that depend, in an essential way, on the holomorphic
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 5
structure of the given Riemann surface, while multiradial algorithms correspond
to constructions of holomorphic objects associated to the Riemann surface which
are expressed [perhaps by allowing for certain indeterminacies!] solely in terms of
the underlying real analytic structure of the Riemann surface — cf. Fig. I.3
below; the discussion of Remark 1.9.2. Perhaps the most fundamental motivat-
ing example in this context is the description of “alien holomorphic structures” by
means of the Teichm¨ uller deformations reviewed at the beginning of [IUTchI],
§I4, relative to “unspecified/indeterminate” deformation data [i.e., consisting
of a nonzero square diﬀerential and a dilation factor]. Indeed, for instance, in the
case of once-punctured elliptic curves, by applying well-known facts concerning Te-
ichm¨ uller mappings [cf., e.g., [Lehto], Chapter V, Theorem 6.3], it is not diﬃcult
to formulate the classical result that
“the homotopy class of every orientation-preserving homeomorphism be-
tween pointed compact Riemann surfaces of genus one ‘lifts’ to a unique
Teichm¨ uller mapping”
in terms of the “multiradial formalism” discussed in the present paper [cf. Example
1.7]. [We leave the routine details to the reader.]
abstract algorithms inter-universal Teichm¨ uller theory classical complex
Teichm¨ uller theory
uniradial algorithms arithmetic holomorphic structures holomorphic
structures
multiradial algorithms arithmetic holomorphic structures described in terms of underlying mono-analytic structures holomorphic
structures described in
terms of underlying
real analytic structures
coric algorithms underlying mono-analytic structures underlying real analytic
structures
Fig. I.3: Uniradiality, Multiradiality, and Coricity
One interesting aspect of the theory of the present series of papers may be seen
in the set-theoretic function arising from the theta values considered above
j2
j → q
v
— a function that is reminiscent of the Gaussian distribution (R ∋) x →
e−x2 on the real line. From this point of view, the passage from the Frobenius-
picture to the canonical splittings of the´ etale-picture [cf. the discussion of [IUTchI],
e−x2
dx= √π
6 SHINICHI MOCHIZUKI
§I1], i.e., in eﬀect, the computation of the Θ-links that occur in the Frobenius-
picture by means of the various multiradial algorithms that will be established in
the present series of papers, may be thought of [cf. the diagram of Fig. I.2!] as a
sort of global arithmetic/Galois-theoretic analogue of the computation of the
classical Gaussian integral
∞
−∞
viathepassagefromcartesian coordinates,i.e.,whichcorrespondtotheFrobenius-
picture, to polar coordinates, i.e., which correspond to the´ etale-picture — cf.
the discussion of Remark 1.12.5.
One way to understand the diﬀerence between coricity, multiradiality, and
uniradiality at a purely combinatorial level is by considering the Fl- and F ±
l-
symmetries discussed in [IUTchI], §I1 [cf. the discussion of Remark 4.7.4 of the
present paper]. Indeed, at a purely combinatorial level, the Fl -symmetry may be
thought of as consisting of the natural action of Fl on the set of labels |Fl|=
{0} Fl [cf. the discussion of [IUTchI], §I1]. Here, the label 0 corresponds to
the [mono-analytic] core. Thus, the corresponding ´ etale-picture consists of various
copies of |Fl|gluedtogetheralongthecoric label 0[cf. Fig. I.4below]. Inparticular,
the various actions of copies of Fl on corresponding copies of |Fl| are “compatible
with simultaneous execution” in the sense that they commute with one another.
That is to say, at least at the level of labels, the Fl -symmetry is multiradial.
... ...
|
— 0 —
Fig. I.4:
´
Etale-picture of Fl -symmetries
...
± ±
± ±
± ±
± ±...
↓ ↑
→
← 0 ←
→
± ±
± ±
Fig. I.5:
´
Etale-picture of F ±
l -symmetries
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 7
Inasimilarvein, atapurelycombinatoriallevel, theF ±
l -symmetrymaybethought
of as consisting of the natural action of F ±
l on the set of labels Fl [cf. the discussion
of [IUTchI], §I1]. Here again, the label 0 corresponds to the [mono-analytic] core.
Thus, the corresponding´ etale-picture consists of various copies of Fl glued together
along the coric label 0 [cf. Fig. I.5 above]. In particular, the various actions of
copies of F ±
l on corresponding copies of Fl are “incompatible with simultaneous
execution” in the sense that they clearly fail to commute with one another. That is
to say, at least at the level of labels, the F ±
l -symmetry is uniradial.
Since, ultimately, in the present series of papers, we shall be interested in the
establishment of multiradial algorithms, “special care” will be necessary in order
to obtain multiradial algorithms for constructing objects related to the a priori
uniradial F ±
l -symmetry [cf. the discussion of Remark 4.7.3 of the present paper;
[IUTchIII], Remark 3.11.2, (i), (ii)]. The multiradiality of such algorithms will be
closely related to the fact that the F ±
l -symmetry is applied to relate the various
copies of local units modulo torsion, i.e., “O×μ” [cf. the notation of [IUTchI],
§1] at various labels ∈ Fl that lie in various spokes of the ´ etale-picture [cf. the
discussion of Remark 4.7.3, (ii)]. This contrasts with the way in which the a pri-
ori multiradial Fl -symmetry will be applied, namely to treat various “weighted
volumes” corresponding to the local value groups and global realified Frobenioids
at various labels ∈ Fl that lie in various spokes of the ´ etale-picture [cf. the dis-
cussion of Remark 4.7.3, (iii)]. Relative to the analogy between the theory of the
present series of papers and p-adic Teichm¨ uller theory [cf. [IUTchI], §I4], various
aspects of the F ±
l -symmetry are reminiscent of the additive monodromy over
the ordinary locus of the canonical curves that occur in p-adic Teichm¨ uller the-
ory; in a similar vein, various aspects of the Fl -symmetry may be thought of as
corresponding to the multiplicative monodromy at the supersingular points of
the canonical curves that occur in p-adic Teichm¨ uller theory — cf. the discussion
of Remark 4.11.4, (iii); Fig. I.7 below.
Before discussing the theory of multiradiality in the context of the theory
of Hodge-Arakelov-theoretic evaluation theory developed in the present paper, we
pause to review the theory of mono-theta environments developed in [EtTh].
One starts with a Tate curve over a mixed-characteristic nonarchimedean local
field. The mono-theta environment associated to such a curve is, roughly speak-
ing, the Kummer-theoretic data that arises by extracting N-th roots of the theta
trivialization of the ample line bundle associated to the origin over suitable tem-
pered coverings of the curve [cf. [EtTh], Definition 2.13, (ii)]. Such mono-theta
environments may be constructed purely group-theoretically from the [arithmetic]
tempered fundamental group of the once-punctured elliptic curve determined by the
given Tate curve [cf. [EtTh], Corollary 2.18], or, alternatively, purely category-
theoretically from the tempered Frobenioid determined by the theory of line bundles
and divisors over tempered coverings of the Tate curve [cf. [EtTh], Theorem 5.10,
(iii)]. Indeed, the isomorphism of mono-theta environments between the mono-
theta environments arising from these two constructions of mono-theta environ-
ments — i.e., from tempered fundamental groups, on the one hand, and from tem-
pered Frobenioids, on the other [cf. Proposition 1.2 of the present paper] — may be
thought of as a sort of Kummer isomorphism for mono-theta environments
[cf. Proposition 3.4 of the present paper, as well as [IUTchIII], Proposition 2.1,
(iii)]. One important consequence of the theory of [EtTh] asserts that mono-theta
8 SHINICHI MOCHIZUKI
environments satisfy the following three rigidity properties:
(a) cyclotomic rigidity,
(b) discrete rigidity, and
(c) constant multiple rigidity
— cf. the Introduction to [EtTh].
Discrete rigidity assuresonethatonemayworkwithZ-translates [wherewe
write Z for the copy of “Z” that acts as a group of covering transformations on the
tempered coverings involved], as opposed to Z-translates [i.e., where Z∼
= Z denotes
the profinite completion of Z], of the theta function, i.e., one need not contend
with Z-powers of canonical multiplicative coordinates [i.e., “U”], or q-parameters
[cf. Remark 3.6.5, (iii); [IUTchIII], Remark 2.1.1, (v)]. Although we will certainly
“use” this discrete rigidity throughout the theory of the present series of papers,
this property of mono-theta environments will not play a particularly prominent
role in the theory of the present series of papers. The Z-powers of “U” and “q” that
would occur if one does not have discrete rigidity may be compared to the PD-
formal series thatareobtained, a priori, ifoneattemptstoconstructthecanonical
parameters of p-adic Teichm¨ uller theory via formal integration. Indeed, PD-formal
power series become necessary if one attempts to treat such canonical parameters
as objects which admit arbitrary O-powers, where O denotes the completion of the
local ring to which the canonical parameter belongs [cf. the discussion of Remark
3.6.5, (iii); Fig. I.6 below].
Constant multiple rigidity plays a somewhat more central role in the
present series of papers, in particular in relation to the theory of the log-link, which
we shall discuss in [IUTchIII] [cf. the discussion of Remark 1.12.2 of the present
paper; [IUTchIII], Remark 1.2.3, (i); [IUTchIII], Proposition 3.5, (ii); [IUTchIII],
Remark 3.11.2, (iii)]. Constant multiple rigidity asserts that the multiplicative
monoid
O×
Fv
· ΘN
v
— which we shall refer to as the theta monoid — generated by the reciprocal
of the l-th root of the theta function and the group of units of the ring of inte-
gers of the base field Fv [cf. the notation of [IUTchI], §I1] admits a canonical
splitting, up to 2l-th roots of unity, that arises from evaluation at the [2-]torsion
point corresponding to the label 0 ∈ Fl [cf. Corollary 1.12, (ii); Proposition 3.1,
(i); Proposition 3.3, (i)]. Put another way, this canonical splitting is the splitting
determined, up to 2l-th roots of unity, by Θv
∈ O×
· ΘN
. The theta monoid of
Fv
v
the above display, as well as the associated canonical splitting, may be constructed
algorithmically from the mono-theta environment [cf. Proposition 3.1, (i)]. Rela-
tive to the analogy between the theory of the present series of papers and p-adic
Teichm¨ uller theory, these canonical splittings may be thought of as corresponding
to the canonical coordinates of p-adic Teichm¨ uller theory, i.e., more precisely,
to the fact that such canonical coordinates are also completely determined without
any constant multiple indeterminacies — cf. Fig. I.6 below; Remark 3.6.5, (iii);
[IUTchIII], Remark 3.12.4, (i).
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 9
Mono-theta-theoretic rigidity property in inter-universal Teichm¨ uller theory Corresponding phenomenon in
p-adic Teichm¨ uller theory
mono-theta-theoretic constant multiple rigidity lack of constant multiple
indeterminacy of
canonical coordinates
on canonical curves
mono-theta-theoretic cyclotomic rigidity lack of Z×-power indeterminacy
of canonical coordinates
on canonical curves,
Kodaira-Spencer
isomorphism
multiradiality of
mono-theta-theoretic constant multiple, cyclotomic rigidity
Frobenius-invariant
nature of
canonical coordinates
mono-theta-theoretic discrete rigidity formal = “non-PD-formal”
nature of canonical coordinates
on canonical curves
Fig. I.6: Mono-theta-theoretic rigidity properties in inter-universal Teichm¨ uller
theory and corresponding phenomena in p-adic Teichm¨ uller theory
Cyclotomic rigidity consists of a rigidity isomorphism, which may be con-
structed algorithmically from the mono-theta environment, between
· the portion of the mono-theta environment — which we refer to as the
exterior cyclotome — that arises from the roots of unity of the base
field and
· a certain copy of the once-Tate-twisted Galois module “Z(1)” — which
we refer to as the interior cyclotome — that appears as a subquotient
of the geometric tempered fundamental group
[cf. Definition 1.1, (ii); Remark 1.1.1; Proposition 1.3, (i)]. This rigidity is remark-
able — as we shall see in our discussion below of the corresponding multiradiality
10 SHINICHI MOCHIZUKI
property — in that unlike the “conventional” construction of such cyclotomic rigid-
ity isomorphisms via local class field theory [cf. Proposition 1.3, (ii)], which requires
one to use the entire monoid with Galois action Gv O◃
, the only portion of
Fv
the monoid O◃
that appears in this construction is the portion [i.e., the “exterior
Fv
cyclotome”] corresponding to the torsion subgroup Oμ
⊆ O◃
[cf. the notation
Fv
Fv
of [IUTchI], §I1]. This construction depends, in an essential way, on the com-
mutator structure of theta groups, but constitutes a somewhat diﬀerent approach
to utilizing this commutator structure from the “classical approach” involving irre-
ducibility of representations of theta groups [cf. Remark 3.6.5, (ii); the Introduction
to [EtTh]]. One important aspect of this dependence on the commutator structure
of the theta group is that the theory of cyclotomic rigidity yields an explanation
for the importance of the special role played by the first power of [the reciprocal
of the l-th root of] the theta function in the present series of papers [cf. Remark
3.6.4, (iii), (iv), (v); the Introduction to [EtTh]]. Relative to the analogy between
the theory of the present series of papers and p-adic Teichm¨ uller theory, mono-
theta-theoretic cyclotomic rigidity may be thought of as corresponding either to
the fact that the canonical coordinates of p-adic Teichm¨ uller theory are completely
determined without any Z×-power indeterminacies or [roughly equivalently] to the
Kodaira-Spencer isomorphism of the canonical indigenous bundle — cf. Fig.
I.6; Remark 3.6.5, (iii); Remark 4.11.4, (iii), (b).
The theta monoid
O×
Fv
· ΘN
v
discussed above admits both´ etale-like and Frobenius-like [i.e., Frobenioid-theo-
retic] versions, which may be related to one another via a Kummer isomorphism
[cf. Proposition 3.3, (i)]. The unit portion, together with its natural Galois action,
of the Frobenioid-theoretic version of the theta monoid
Gv O×
Fv
forms the portion at v ∈ Vbad of the F⊢×-prime-strip“F⊢×
mod” that is preserved,
up to isomorphism, by the Θ-link [cf. the discussion of [IUTchI], §I1; [IUTchI],
Theorem A, (ii)]. In the theory of the present paper, we shall introduce modified
versions of the Θ-link of [IUTchI] [cf. the discussion of the “Θ×μ-, Θ×μ
gau-links”
below], which, unlike the Θ-link of [IUTchI], only preserve [up to isomorphism] the
F⊢×μ-prime-strips — i.e., which consist of the data
Gv O×μ
Fv
= O×
/Oμ
Fv
Fv
[cf. the notation of [IUTchI], §I1] at v ∈ Vbad — associated to the F⊢×-prime-
strips preserved [up to isomorphism] by the Θ-link of [IUTchI]. Since this data is
only preserved up to isomorphism, it follows that the topological group “Gv” must
beregardedasbeingonly known up to isomorphism, whilethemonoidO×μ
mustbe
Fv
regarded as being only known up to [the automorphisms of this monoid determined
by the natural action of] Z×. That is to say, one must regard
the data Gv O×μ
as subject to Aut(Gv)-, Z×-indeterminacies.Fv
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 11
These indeterminacies will play an important role in the theory of the present series
ofpapers—cf. theindeterminacies“(Ind1)”, “(Ind2)”of[IUTchIII],Theorem3.11,
(i).
Now let us return to our discussion of the various mono-theta-theoretic rigidity
properties. The key observation concerning these rigidity properties, as reviewed
above, in the context of the Aut(Gv)-, Z×-indeterminacies just discussed, is the
following:
thecanonical splittings, via“evaluation at the zero section”, ofthetheta
monoids, together with the construction of the mono-theta-theoretic
cyclotomic rigidity isomorphism, are compatible with, in the sense
that they are left unchanged by, the Aut(Gv)-, Z×-indeterminacies dis-
cussed above
— cf. Corollaries 1.10, 1.12; Proposition 3.4, (i). Indeed, this observation consti-
tutes the substantive content of the multiradiality of mono-theta-theoretic con-
stant multiple/cyclotomic rigidity [cf. Fig. I.6] and will play an important role
in the statements and proofs of the main results of the present series of papers
[cf. [IUTchIII], Theorem 2.2; [IUTchIII], Corollary 2.3; [IUTchIII], Theorem 3.11,
(iii), (c); Step (ii) of the proof of [IUTchIII], Corollary 3.12]. At a technical level,
this “key observation” simply amounts to the observation that the only portion of
the monoid O×
that is relevant to the construction of the canonical splittings and
Fv
cyclotomic rigidity isomorphism under consideration is the torsion subgroup Oμ
Fv
,
which [by definition!] maps to the identity element of O×μ
, hence is immune to
Fv
the various indeterminacies under consideration. That is to say, the multiradiality
of mono-theta-theoretic constant multiple/cyclotomic rigidity may be regarded as
an essentially formal consequence of the triviality of the natural homomorphism
Oμ
Fv
→ O×μ
Fv
[cf. Remark 1.10.2].
After discussing, in §1, the multiradiality theory surrounding the various rigid-
ity properties of the mono-theta environment, we take up the task, in §2 and §3, of
establishingthetheoryofHodge-Arakelov-theoretic evaluation, i.e., ofpassing
[for v ∈ Vbad]
O×
Fv
· ΘN
v
O×
Fv
j2
· {q
}N
j=1,...,l
v
from theta monoids as discussed above [i.e., the monoids on the left-hand side of
the above display] to Gaussian monoids [i.e., the monoids on the right-hand side
oftheabovedisplay]bymeansoftheoperationof“evaluation” at l-torsion points.
Just as in the case of theta monoids, Gaussian monoids admit both´ etale-like ver-
sions, which constitute the main topic of §2, and Frobenius-like [i.e., Frobenioid-
theoretic] versions, which constitute the main topic of §3. Moreover, as discussed at
the beginning of the present Introduction, it is of crucial importance in the theory
of the present series of papers to be able to relate these´ etale-like and Frobenius-like
versions to one another via Kummer theory. One important observation in this
12 SHINICHI MOCHIZUKI
context — which we shall refer to as the “principle of Galois evaluation” — is
the following: it is essentially a tautology that
this requirement of compatibility with Kummer theory forces any sort
of “evaluation operation” to arise from restriction to Galois sections of
the [arithmetic] tempered fundamental groups involved
[i.e., Galois sections of the sort that arise from rational points such as l-torsion
points!] — cf. the discussion of Remarks 1.12.4, 3.6.2. This tautology is interesting
both in light of the history surrounding the Section Conjecture in anabelian geom-
etry [cf. [IUTchI], §I5] and in light of the fact that the theory of [SemiAnbd] that is
applied to prove [IUTchI], Theorem B — a result which plays an important role in
the theory of §2 of the present paper! [cf. the discussion below] — may be thought
of as a sort of “Combinatorial Section Conjecture”.
At this point, we remark that, unlike the theory of theta monoids discussed
above, the theory of Gaussian monoids developed in the present paper does not,
by itself, admit a multiradial formulation [cf. Remarks 2.9.1, (iii); 3.4.1, (ii); 3.7.1].
In order to obtain a multiradial formulation of the theory of Gaussian monoids —
which is, in some sense, the ultimate goal of the present series of papers! — it
will be necessary to combine the theory of the present paper with the theory of
the log-link developed in [IUTchIII]. This will allow us to obtain a multiradial
formulation of the theory of Gaussian monoids in [IUTchIII], Theorem 3.11.
One important aspect of the theory of Hodge-Arakelov-theoretic evaluation is
the notion of conjugate synchronization. Conjugate synchronization refers to a
collection of “symmetrizing isomorphisms” between the various copies of the local
absolute Galois group Gv associated to the labels ∈ Fl at which one evaluates the
theta function [cf. Corollaries 3.5, (i); 3.6, (i); 4.5, (iii); 4.6, (iii)]. We shall also
use the term “conjugate synchronization” to refer to similar collections of “sym-
metrizing isomorphisms” for copies of various objects [such as the monoid O◃
]
Fv
closely related to the absolute Galois group Gv. With regard to the collections of
isomorphisms between copies of Gv, it is of crucial importance that these isomor-
phisms be completely well-defined, i.e., without any conjugacy indeterminacies!
Indeed, if one allows conjugacy indeterminacies [i.e., put another way, if one allows
oneself to work with outer isomorphisms, as opposed to isomorphisms], then one
must sacrifice either
· the distinct nature of distinct labels ∈ |Fl| — which is necessary in
j2
order to keep track of the distinct theta values “q
” for distinct j— or
· the crucial compatibility of´ etale-like and Frobenius-like versions of the
symmetrizing isomorphisms with Kummer theory
— cf. the discussion of Remark 3.8.3, (ii); [IUTchIII], Remark 1.5.1; Step (vii)
of the proof of [IUTchIII], Corollary 3.12. In this context, it is also of interest to
observe that it follows from certain elementary combinatorial considerations that
one must require that
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 13
· these symmetrizing isomorphisms arise from a group action, i.e., such
as the F ±
l -symmetry
— cf. the discussion of Remark 3.5.2. Moreover, since it will be of crucial impor-
tance to apply these symmetrizing isomorphisms, in [IUTchIII], §1 [cf., especially,
[IUTchIII], Remark 1.3.2], in the context of the log-link — whose definition de-
pends on the local ring structures at v ∈ Vbad [cf. the discussion of [AbsTopIII],
§I3] — it will be necessary to invoke the fact that
· the symmetrizing isomorphisms at v ∈ Vbad arise from conjugation op-
erations within a certain [arithmetic] tempered fundamental group
— namely, the tempered fundamental group of Xv [cf. the notation of
[IUTchI], §I1] — that contains Πv as an open subgroup of finite index
— cf. the discussion of Remark 3.8.3, (ii). Here, we note that these “conjugation
operations” related to the F ±
l -symmetry may be applied to establish conjugate
synchronization precisely because they arise from conjugation by elements of the
geometric tempered fundamental group [cf. Remark 3.5.2, (iii)].
The significance of establishing conjugate synchronization — i.e., subject
to the various requirements discussed above! — lies in the fact that the resulting
symmetrizing isomorphisms allow one to
construct the crucial coric F⊢×μ-prime-strips
— i.e., the F⊢×μ-prime-strips that are preserved, up to isomorphism, by the modi-
fied versions of the Θ-link of [IUTchI] [cf. the discussion of the “Θ×μ-, Θ×μ
gau-links”
below] that are introduced in §4 of the present paper [cf. Corollary 4.10, (i), (iv);
[IUTchIII], Theorem 1.5, (iii); the discussion of [IUTchIII], Remark 1.5.1, (i)].
In §4, the theory of conjugate synchronization established in §3 [cf. Corollaries
3.5, (i); 3.6, (i)] is extended so as to apply to arbitrary v ∈ V, i.e., not just v ∈ Vbad
[cf. Corollaries 4.5, (iii); 4.6, (iii)]. In particular, in order to work with the theta
value labels ∈ Fl in the context of the F ±
l -symmetry, i.e., which involves the
action
F ±
l Fl
on the labels ∈ Fl, one must avail oneself of the global portion of the Θ±ell-Hodge
theaters that appear. Indeed, this global portion allows one to synchronize the a
priori independent indeterminacies with respect to the action of {±1} on the
various X
v [for v ∈ Vbad], X
− →v [for v ∈ Vgood] — cf. the discussion of Remark 4.5.3,
(iii). On the other hand, the copy of the arithmetic fundamental group of XK that
constitutes this global portion of the Θ±ell-Hodge theater is profinite, i.e., it does
not admit a “globally tempered version” whose localization at v ∈ Vbad is naturally
isomorphic to the corresponding tempered fundamental group at v. One important
consequence of this state of aﬀairs is that
in order to apply the global ±-synchronization aﬀorded by the Θ±ell
-
Hodge theater in the context of the theory of Hodge-Arakelov-theoretic
evaluation at v ∈ Vbad relative to labels ∈ Fl that correspond to conju-
gacy classes of cuspidal inertia groups of tempered fundamental groups at
14 SHINICHI MOCHIZUKI
v ∈ Vbad, it is necessary to compute the profinite conjugates of such
tempered cuspidal inertia groups
— cf. the discussion of [IUTchI], Remark 4.5.1, as well as Remarks 2.5.2 and 4.5.3,
(iii), of the present paper, for more details. This is precisely what is achieved by
the application of [IUTchI], Theorem B [i.e., in the form of [IUTchI], Corollary 2.5;
cf. also [IUTchI], Remark 2.5.2] in §2 of the present paper.
As discussed above, the theory of Hodge-Arakelov-theoretic evaluation devel-
oped in §1, §2, §3 is strictly local [at v ∈ Vbad] in nature. Thus, in §4, we discuss
the essentially routine extensions of this theory, e.g., of the theory of Gaussian
monoids, to the “remaining portion” of the Θ±ell-Hodge theater, i.e., to v ∈ Vgood
,
as well as to the case of global realified Frobenioids [cf. Corollaries 4.5, (iv), (v); 4.6,
(iv), (v)]. We also discuss the corresponding complements, involving the theory of
[IUTchI], §5, for ΘNF-Hodge theaters [cf. Corollaries 4.7, 4.8]. This leads naturally
to the construction of modified versions of the Θ-link of [IUTchI] [cf. Corollary
4.10, (iii)]. These modified versions may be described as follows:
· The Θ×μ-link is essentially the same as the Θ-link of [IUTchI], Theorem
A, except that F -prime-strips are replaced by F ×μ-prime-strips [cf.
[IUTchI], Fig. I1.2] — i.e., roughly speaking, the various local “O×” are
replaced by “O×μ = O×/Oμ”.
· The Θ×μ
gau-link is essentially the same as the Θ×μ-link, except that the
theta monoids that give rise to the Θ×μ-link are replaced, via composition
withacertainisomorphismthatarisesfromHodge-Arakelov-theoretic eval-
uation, by Gaussian monoids [cf. the above discussion!] — i.e., roughly
speaking, the various “Θv
” at v ∈ Vbad are replaced by “{q
j2
}j=1,...,l ”.
v
ThebasicpropertiesoftheΘ×μ-,Θ×μ
gau-links,includingthecorrespondingFrobenius-
and´ etale-pictures, are summarized in Theorems A, B below [cf. Corollaries 4.10,
4.11 for more details]. Relative to the analogy between the theory of the present
series of papers and p-adic Teichm¨ uller theory, the passage from the Θ×μ-link to
the Θ×μ
gau-link via Hodge-Arakelov-theoretic evaluation may be thought of as
corresponding to the passage
MF∇-objects Galois representations
in the case of the canonical indigenous bundles that occur in p-adic Teichm¨ uller
theory — cf. the discussion of Remark 4.11.4, (ii), (iii). In particular, the corre-
sponding passage from the Frobenius-picture associated to the Θ×μ-link to the
Frobenius-picture associated to the Θ×μ
gau-link — or, more properly, relative to the
point of view of [IUTchIII] [cf. also the discussion of [IUTchI], §I4], from the
log-theta-lattice arising from the Θ×μ-link to the log-theta-lattice arising from the
Θ×μ
gau-link — corresponds [i.e.., relative to the analogy with p-adic Teichm¨ uller the-
ory] to the passage
from thinking of canonical liftings as being determined by canonical
MF∇-objects to thinking of canonical liftings as being determined by
canonical Galois representations [cf. Fig. I.7 below].
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 15
In this context, it is of interest to note that this point of view is precisely the
point of view taken in the absolute anabelian reconstruction theory developed in
[CanLift], §3 [cf. Remark 4.11.4, (iii), (a)]. Finally, we observe that from this
point of view, the important theory of conjugate synchronization via the F ±
l-
symmetry may be thought of as corresponding to the theory of the deformation
of the canonical Galois representation from “mod pn” to “mod pn+1” [cf. Fig. I.7
below; the discussion of Remark 4.11.4, (iii), (d)].
Property related to Hodge-Arakelov-theoretic evaluation in inter-universal Teichm¨ uller theory
Corresponding phenomenon
in
p-adic Teichm¨ uller theory
passage from to Θ×μ
gau-link passage from
Θ×μ-link canonicality via MF∇-objects
to canonicality via
crystalline Galois representations
F ±
l -, Fl- ordinary, supersingular monodromy
symmetries of canonical Galois representation
conjugate synchronization via F ±
l -symmetry deformation of
canonical Galois representation
from “mod pn” to “mod pn+1”
Fig. I.7: Properties related to Hodge-Arakelov-theoretic evaluation in
inter-universal Teichm¨ uller theory and corresponding phenomena in
p-adic Teichm¨ uller theory
Certain aspects of the various constructions discussed above are summarized
in the following two results, i.e., Theorems A, B, which are abbreviated versions
of Corollaries 4.10, 4.11, respectively. On the other hand, many important aspects
— such as multiradiality! — of these constructions do not appear explicitly in
Theorems A, B. The main reason for this is that it is diﬃcult to formulate “final
results” concerning such aspects as multiradiality in the absence of the framework
that is to be developed in [IUTchIII].
Theorem A. (Frobenius-pictures of Θ±ellNF-Hodge Theaters) Fix a col-
lection of initial Θ-data (F/F, XF, l, CK, V, Vbad
mod, ϵ) as in [IUTchI], Definition
3.1. Let †HT Θ±ellNF
; ‡HT Θ±ellNF be Θ±ellNF-Hodge theaters [relative to the
given initial Θ-data] — cf. [IUTchI], Definition 6.13, (i). Write †HT D-Θ±ellNF
,
16 SHINICHI MOCHIZUKI
‡HT D-Θ±ellNF for the associated D-Θ±ellNF-Hodge theaters — cf. [IUTchI],
Definition 6.13, (ii). Then:
(i) (Constant Prime-Strips) By applying the symmetrizing isomorphisms,
with respect to the F ±
l -symmetry, of Corollary 4.6, (iii), to the data of the un-
derlying Θ±ell-Hodge theater of †HT Θ±ellNF that is labeled by t ∈ LabCusp±(†D≻),
one may construct, in a natural fashion, an F -prime-strip
†F△ = (†C△, Prime(†C△)∼
→ V,
†F⊢
△, {†ρ△,v}v∈V)
that is equipped with a natural identification isomorphism of F -prime-strips
†F△
∼
→ †Fmod between †F△ and the F -prime-strip †Fmod of [IUTchI], Theorem
A, (ii); this isomorphism induces a natural identification isomorphism of D⊢
-
prime-strips †D⊢
∼
→ †D⊢
△
> between the D⊢-prime-strip †D⊢
△ associated to †F△ and
the D⊢-prime-strip †D⊢
> of [IUTchI], Theorem A, (iii).
(ii) (Theta and Gaussian Prime-Strips) By applying the constructions
of Corollary 4.6, (iv), (v), to the underlying Θ-bridge and Θ±ell-Hodge theater of
†HT Θ±ellNF, one may construct, in a natural fashion, F -prime-strips
†Fenv = (†Cenv, Prime(†Cenv)∼
→ V,
†F⊢
env, {†ρenv,v}v∈V)
†Fgau = (†Cgau, Prime(†Cgau)∼
→ V,
†F⊢
gau, {†ρgau,v}v∈V)
that are equipped with a natural identification isomorphism of F -prime-strips
†Fenv
∼
→ †Ftht between †Fenv and the F -prime-strip †Ftht of [IUTchI], Theorem
A, (ii), as well as an evaluation isomorphism
†Fenv
∼
→ †Fgau
of F -prime-strips.
(iii) (Θ×μ- and Θ×μ
gau-Links) Write ‡F ×μ
△ (respectively, †F ×μ
env ; †F ×μ
gau )
for the F ×μ-prime-strip associated to the F -prime-strip ‡F△ (respectively,
†Fenv; †Fgau). We shall refer to the full poly-isomorphism †F ×μ
∼
env
→ ‡F ×μ
△ as
the Θ×μ-link
†HT Θ±ellNF Θ×μ
−→ ‡HT Θ±ellNF
[cf. the “Θ-link” of [IUTchI], Theorem A, (ii)] from †HT Θ±ellNF to ‡HT Θ±ellNF
,
and to the full poly-isomorphism †F ×μ
∼
→ ‡F ×μ
gau
△ — which may be regarded as
being obtained from the full poly-isomorphism †F ×μ
∼
env
→ ‡F ×μ
△ by composition
with the inverse of the evaluation isomorphism of (ii) — as the Θ×μ
gau-link
†HT Θ±ellNF Θ×μ
gau −→ ‡HT Θ±ellNF
from †HT Θ±ellNF to ‡HT Θ±ellNF
.
(iv) (Coric F⊢×μ-Prime-Strips) The definition of the unit portion of the
theta and Gaussian monoids that appear in the construction of the F -prime-
strips †Fenv,
†Fgau of (ii) gives rise to natural isomorphisms
†F⊢×μ
∼
△
→ †F⊢×μ
∼
env
→ †F⊢×μ
gau
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 17
of the F⊢×μ-prime-strips associated to the F -prime-strips †F△,
†Fenv,
†Fgau.
Moreover, by composing these natural isomorphisms with the poly-isomorphisms
induced on the respective F⊢×μ-prime-strips by the Θ×μ- and Θ×μ
gau-links of (iii),
one obtains a poly-isomorphism
†F⊢×μ
△
∼
→ ‡F⊢×μ
△
which coincides with the full poly-isomorphism between these two F⊢×μ-prime-
strips — that is to say, “(−)F⊢×μ
△ ” is an invariant of both the Θ×μ- and Θ×μ
gau-links.
Finally, this full poly-isomorphism induces the full poly-isomorphism
†D⊢
△
∼
→ ‡D⊢
△
between the associated D⊢-prime-strips; we shall refer to this poly-isomorphism as
the D-Θ±ellNF-link from †HT D-Θ±ellNF to ‡HT D-Θ±ellNF
.
(v) (Frobenius-pictures) Let {nHT Θ±ellNF}n∈Z be a collection of distinct
Θ±ellNF-Hodge theaters indexed by the integers. Then by applying the Θ×μ-
and Θ×μ
gau-links of (iii), we obtain infinite chains
Θ×μ
...
−→ (n−1)HT Θ±ellNF Θ×μ
−→ nHT Θ±ellNF Θ×μ
−→ (n+1)HT Θ±ellNF Θ×μ
−→...
Θ×μ
...
gau −→ (n−1)HT Θ±ellNF Θ×μ
gau −→ nHT Θ±ellNF Θ×μ
gau −→ (n+1)HT Θ±ellNF Θ×μ
gau −→...
of Θ×μ-/Θ×μ
gau-linked Θ±ellNF-Hodge theaters — cf. Fig. I.8 below, in the case
of the Θ×μ
gau-link. Either of these infinite chains may be represented symbolically as
an oriented graph⃗
Γ
... → • → • → • →...
— i.e., where the arrows correspond to either the “ Θ×μ
Θ×μ
−→ ’s” or the “
gau −→ ’s”, and
the “•’s” correspond to the “nHT Θ±ellNF”. This oriented graph⃗
Γ admits a natural
action by Z — i.e., a translation symmetry — but it does not admit arbitrary
permutation symmetries. For instance,⃗
Γ does not admit an automorphism that
switches two adjacent vertices, but leaves the remaining vertices fixed.
- -
...
nq
v
nHT Θ±ellNF
nq
12
.
.
(l )2
.
v
- -
(n+1)q
v
(n+1)HT Θ±ellNF
(n+1)q
v
12
.
.
(l )2
.
- -
...
nq
.
.
.
v
→ (n+1)q
v
Fig. I.8: Frobenius-picture associated to the Θ×μ
gau-link
18 SHINICHI MOCHIZUKI
´
Theorem B. (
Etale-pictures of Base-Θ±ellNF-Hodge Theaters) Suppose
that we are in the situation of Theorem A, (v).
(i) Write
D
...
−→ nHT D-Θ±ellNF D
−→ (n+1)HT D-Θ±ellNF D
−→...
— where n ∈ Z — for the infinite chain of D-Θ±ellNF-linked D-Θ±ellNF-
Hodge theaters [cf. Theorem A, (iv), (v)] induced by either of the infinite
chains of Theorem A, (v). Then this infinite chain induces a chain of full poly-
isomorphisms
∼
...
→ nD⊢
△
∼
→ (n+1)D⊢
△
∼
→...
[cf. Theorem A, (iv)]. That is to say, “(−)D⊢
△” forms a constant invariant—
i.e., a “mono-analytic core” [cf. the discussion of [IUTchI], §I1] — of the above
infinite chain.
(ii) If we regard each of the D-Θ±ellNF-Hodge theaters of the chain of (i) as a
spoke emanating from the mono-analytic core “(−)D⊢
△” discussed in (i), then we
obtain a diagram — i.e., an´ etale-picture of D-Θ±ellNF-Hodge theaters — as
in Fig. I.9 below [cf. the situation discussed in [IUTchI], Theorem A, (iii)]. Thus,
each spoke may be thought of as a distinct “arithmetic holomorphic struc-
ture” on the mono-analytic core. Finally, [cf. the situation discussed in [IUTchI],
Theorem A, (iii)] this diagram satisfies the important property of admitting arbi-
trary permutation symmetries among the spokes [i.e., the labels n ∈ Z of the
D-Θ±ellNF-Hodge theaters].
(iii) The constructions of (i) and (ii) are compatible, in the evident sense,
with the constructions of [IUTchI], Theorem A, (iii), relative to the natural iden-
tification isomorphisms (−)D⊢
∼
→ (−)D⊢
△
> [cf. Theorem A, (i)].
nHT D-Θ±ellNF
...
|...
n
′HT D-Θ±ellNF
— (−)D⊢
△
—
n
′′HT D-Θ±ellNF
...
|
...
n
′′′HT D-Θ±ellNF
Fig. I.9:
´
Etale-picture of D-Θ±ellNF-Hodge theaters
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 19
Acknowledgements:
The research discussed in the present paper profited enormously from the gen-
eroussupportthattheauthorreceivedfromtheResearch Institute for Mathematical
Sciences, aJointUsage/ResearchCenterlocatedinKyotoUniversity. Atapersonal
level, I would like to thank Fumiharu Kato, Akio Tamagawa, Go Yamashita, Mo-
hamed Sa¨ ıdi, Yuichiro Hoshi, Ivan Fesenko, Fucheng Tan, Emmanuel Lepage, Arata
Minamide, and Wojciech Porowski for many stimulating discussions concerning the
material presented in this paper. Also, I feel deeply indebted to Go Yamashita,
Mohamed Sa¨ ıdi, and Yuichiro Hoshi for their meticulous reading of and numerous
comments concerning the present paper. Finally, I would like to express my deep
gratitude to Ivan Fesenko for his quite substantial eﬀorts to disseminate — for in-
stance, in the form of a survey that he wrote — the theory discussed in the present
series of papers.
Notations and Conventions:
We shall continue to use the “Notations and Conventions” of [IUTchI], §0.
20 SHINICHI MOCHIZUKI
Section 1: Multiradial Mono-theta Environments
In the present §1, we review the theory of mono-theta environments devel-
oped in [EtTh] and give a “multiradial” interpretation of this theory, which will
be of substantial importance in the present series of papers. Roughly speaking, in
the language of [AbsTopIII], §I3, this interpretation consists of the computation of
which portion of the various objects constructed from the “arithmetic holomorphic
structures” of various Θ±ellNF-Hodge theaters may be glued together, in a fashion
consistent with the constructions of the objects of interest, via a “mono-analytic”
[i.e., “arithmetic real analytic”] core. Put another way, this computation may be
thought of as the computation of
what one arithmetic holomorphic structure looks like from the point of
view of a distinct arithmetic holomorphic structure that is only related to
the original arithmetic holomorphic structure via the mono-analytic core.
In fact, this sort of computation forms one of the central themes of the present
series of papers.
Let N ∈ N≥1 be a positive integer; l an odd prime number; k an MLF of
odd residue characteristic p ̸= l that contains a primitive 4l-th root of unity; k an
algebraic closure of k;
Xk
a hyperbolic curve of type (1,(Z/lZ)Θ) [cf. [EtTh], Definition 2.5, (i)] over k that
admits a stable model over the ring of integers Ok of k; Xk → Ck the k-core
determined by Xk [cf. the discussion at the beginning of [EtTh], §2]. Write Πtp
X
k
for the tempered fundamental group of Xk; Gk
def = Gal(k/k); Δtp
X
def = Ker(Πtp
X
k
k
Gk) ⊆ Πtp
X
for the geometric tempered fundamental group of Xk. We shall use
k
similar notation for objects associated to Ck.
Definition 1.1. Let
MΘ
be a mod N mono-theta environment [cf. [EtTh], Definition 2.13, (ii)] which is
isomorphic to the mod N model mono-theta environment determined by Xk; write
ΠMΘ
for the underlying topological group of MΘ [cf. [EtTh], Definition 2.13, (ii), (a)].
Then:
(i) There exist functorial algorithms
MΘ → ΠY (MΘ); MΘ → ΠX(MΘ); MΘ → G(MΘ); MΘ → ΔMΘ;
MΘ → ΔY (MΘ); MΘ → ΔX(MΘ); MΘ → (l·ΔΘ)(MΘ); MΘ → Πμ(MΘ)
for constructing from MΘ a quotient ΠMΘ ΠY (MΘ) [cf. [EtTh], Corollary
2.18, (iii)]; a topological group ΠX(MΘ) which is isomorphic to Πtp
and con-
X
k
tains ΠY (MΘ) as a normal open subgroup [cf. [EtTh], Corollary 2.18, (iii)]; a
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 21
quotient ΠX(MΘ) G(MΘ) corresponding to Gk [cf. [EtTh], Corollary 2.18,
(i)], which may also be thought of as a quotient ΠMΘ ΠY (MΘ) G(MΘ); a
closed normal subgroup ΔMΘ
def = Ker(ΠMΘ G(MΘ)) ⊆ ΠMΘ; a closed normal
subgroup ΔY (MΘ) def = Ker(ΠY (MΘ) G(MΘ)) ⊆ ΠY (MΘ); a closed normal sub-
group ΔX(MΘ) def = Ker(ΠX(MΘ) G(MΘ)) ⊆ ΠX(MΘ) corresponding to Δtp
X
[cf.
k
[EtTh], Corollary 2.18, (i)]; a subquotient (l·ΔΘ)(MΘ) of ΠY (MΘ) which admits a
natural ΠX(MΘ)-action [hence also a ΠY (MΘ)-action, as well as, by composition, a
ΠMΘ-action] relative to which it is abstractly isomorphic to Z(1) [cf. [EtTh], Corol-
lary 2.18, (i)]; a closed normal subgroup Πμ(MΘ) def = Ker(ΠMΘ ΠY (MΘ)) ⊆ ΠMΘ
[cf. [EtTh], Corollary 2.19, (i)] which admits a natural ΠX(MΘ)-action [hence also
a ΠY (MΘ)-action, as well as, by composition, a ΠMΘ-action] relative to which it
is abstractly isomorphic to (Z/NZ)(1). Also, we recall that the structure of MΘ
determines a lifting of the natural outer action of
(l·Z)(MΘ) def = ΠX(MΘ)/ΠY (MΘ)∼
= ΔX(MΘ)/ΔY (MΘ)
on ΔY (MΘ) to an outer action of (l·Z)(MΘ) on ΔMΘ [cf. [EtTh], Definition 2.13,
(i), (ii), and the preceding discussion; [EtTh], Proposition 2.14, (i)].
(ii) We shall refer to (l· ΔΘ)(MΘ) (respectively, Πμ(MΘ)) as the interior
(respectively, exterior) cyclotome associated to MΘ. By [EtTh], Corollary 2.19,
(i), there is a functorial algorithm for constructing from MΘ a cyclotomic rigidity
isomorphism
(l·ΔΘ)(MΘ)⊗(Z/NZ)∼
→ Πμ(MΘ)
between the reductions modulo N of the interior and exterior cyclotomes associated
to MΘ
.
Remark 1.1.1. In light of its importance in the present series of papers, we
pause to review the mono-theta-theoretic cyclotomic rigidity isomorphism
of Definition 1.1, (ii), in more detail, as follows.
(i) First, we recall from [EtTh], Proposition 2.4 [cf. also the construction of the
covering “Ylog → Xlog” at the beginning of [EtTh], §1], that the topological group
ΠX(MΘ) determines topological groups ΠY (MΘ), ΠX(MΘ), and ΠC(MΘ) — i.e.,
corresponding to the coverings “Ylog → Xlog → Clog” of the discussion preceding
[EtTh], Definition 2.7 — all of which [together with ΠX(MΘ)] may be regarded as
open subgroups of ΠC(MΘ)
ΠY (MΘ) ⊆ ΠX(MΘ) ⊆ ΠC(MΘ) (⊇ ΠX(MΘ) ⊇ ΠX(MΘ))
that are equipped with compatible surjections to G(MΘ). Write
ΔY (MΘ) ⊆ ΔX(MΘ) ⊆ ΔC(MΘ) (⊇ ΔX(MΘ) ⊇ ΔX(MΘ))
for the respective kernels of these surjections. Moreover, the various topological
groups of the above two displays are equipped with subquotients denoted by means
22 SHINICHI MOCHIZUKI
of a superscript “Θ” or a superscript “ell” [cf. the discussion at the beginning of
[EtTh], §1]. Thesesubquotientsarecompletelydeterminedbythetopologicalgroup
structure of ΠC(MΘ) [cf. the discussion at the beginning of [EtTh], §1; the proof of
[EtTh], Proposition 1.8]. For instance, we observe that one may reconstruct from
the topological group ΠX(MΘ) [cf. [EtTh], Corollary 2.18, (i)] the quotient
ΠMΘ ΠY (MΘ) Πell
Y (MΘ)
[which isomorphic to Z(1) Gk, relative to the natural cyclotomic action of Gk
on Z(1)] corresponding to the quotient “Πtp
Y (Πtp
Y )ell” of the discussion at the
beginning of [EtTh], §1.
(ii)ObservethatanyclosedsubgroupH ⊆ ΠY (MΘ)determines,byformingthe
inverse image via the quotient ΠMΘ ΠY (MΘ), a closed subgroup ΠMΘ|H ⊆ ΠMΘ.
On the other hand, by forming the quotient of ΠMΘ by the restriction of the “theta
section portion” of the mono-theta environment MΘ [cf. [EtTh], Definition 2.13,
(ii), (c)] to the subgroup Ker(ΠY (MΘ) ΠΘ
Y (MΘ)) ⊆ ΠY (MΘ), it makes sense to
speak of the quotient of ΠMΘ
(ΠMΘ ) ΠMΘ|ΠΘ
Y (MΘ) ( ΠΘ
Y (MΘ))
determined by the quotient ΠY (MΘ) ΠΘ
Y (MΘ) — cf. the discussion at the
beginning of the proof of [EtTh], Corollary 2.19, (i). In particular, it makes sense
to speak of the subquotient of ΠMΘ determined by any closed subgroup — i.e., such
as (l·ΔΘ)(MΘ) ⊆ ΠΘ
Y (MΘ) — of ΠΘ
Y (MΘ).
(iii) In addition to the subgroup
Πμ(MΘ) → ΠMΘ|(l·ΔΘ)(MΘ)
determined by the subgroup Πμ(MΘ) ⊆ ΠMΘ of Definition 1.1, (i), the “theta
section portion” of the mono-theta environment MΘ [cf. [EtTh], Definition 2.13,
(ii), (c)] determines, by restriction, a subgroup
sΘ(MΘ)|(l·ΔΘ)(MΘ) ⊆ ΠMΘ|(l·ΔΘ)(MΘ)
that maps isomorphically to (l·ΔΘ)(MΘ) via the natural projection ΠMΘ|(l·ΔΘ)(MΘ)
(l·ΔΘ)(MΘ) [cf. the proof of [EtTh], Corollary 2.19, (i)]. On the other hand,
by considering liftings γ of automorphisms of ΔY (MΘ) determined by conjugation
by elements of ΔX(MΘ) to automorphisms of ΠMΘ that determine outer automor-
phisms of the sort that appear in the definition of a mono-theta environment [cf.
[EtTh], Definition 2.13, (ii), (b)] and then forming the “commutator γ(β)·β−1” of
such liftings with arbitrary elements β ∈ ΔY (MΘ) [cf. [EtTh], Proposition 2.14,
(i)], one obtains a natural bilinear “commutator map”
[−
,−] : (ΔX(MΘ)/ΔY (MΘ)) × Δell
Y (MΘ) → ΠMΘ|(l·ΔΘ)(MΘ)
— where we recall that (l·Z)∼
→ ΔX(MΘ)/ΔY (MΘ) is abstractly isomorphic to Z,
while Δell
Y (MΘ) is abstractly isomorphic to Z — whose image determines a subgroup
salg(MΘ)|(l·ΔΘ)(MΘ) ⊆ ΠMΘ|(l·ΔΘ)(MΘ)
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 23
that maps isomorphically to (l·ΔΘ)(MΘ) via the natural projection ΠMΘ|(l·ΔΘ)(MΘ)
(l· ΔΘ)(MΘ) [cf. the proof of [EtTh], Corollary 2.19, (i)]. The mono-theta-
theoretic cyclotomic rigidity isomorphism of Definition 1.1, (ii), is then re-
constructed [cf. [EtTh], Corollary 2.19, (i)] by forming the diﬀerence of the two
sections sΘ(MΘ)|(l·ΔΘ)(MΘ), salg(MΘ)|(l·ΔΘ)(MΘ).
(iv)Next, weobservethatthemono-theta-theoreticcyclotomicrigidityisomor-
phism of Definition 1.1, (ii), admits a certain symmetry with respect to the group
ΔC(MΘ)/ΔX(MΘ)∼
= F ±
l [cf. [IUTchI], Definition 6.1, (v)], as follows. First of all,
let us observe that the natural conjugation action of ΠY (MΘ) on ΠMΘ|(l·ΔΘ)(MΘ)
factors through the natural surjection ΠY (MΘ) G(MΘ). In particular, by ap-
plying the natural surjection ΠC(MΘ) G(MΘ), one may regard ΠMΘ|(l·ΔΘ)(MΘ)
as being equipped with a “naively defined” action by ΠC(MΘ). On the other hand,
let us recall from the discussion preceding [EtTh], Definition 2.13, that the “model”
for ΠMΘ is originally constructed as the subgroup
Πμ(MΘ) ΠY (MΘ) ⊆ Πμ(MΘ) ΠC(MΘ)
— where the semi-direct products are formed relative to the natural cyclotomic
action of ΠC(MΘ). Here, the evident subquotient Πμ(MΘ) (l· ΔΘ)(MΘ) of
Πμ(MΘ) ΠC(MΘ) — i.e., which corresponds to the subquotient ΠMΘ|(l·ΔΘ)(MΘ) of
ΠMΘ — is easily verified to be stabilized by the action via conjugation of Πμ(MΘ)
ΠC(MΘ). Moreover, one verifies easily that this conjugation action of Πμ(MΘ)
ΠC(MΘ)factorsthroughthenaturalquotientΠμ(MΘ) ΠC(MΘ) ΠC(MΘ)
G(MΘ)andcoincideswiththeactionofG(MΘ)viathecyclotomic character G(MΘ)
→ Z× on the abelian profinite group Πμ(MΘ) (l· ΔΘ)(MΘ) [where we re-
call that Z× acts tautologically on any abelian profinite group]. That is to say,
in summary, even if one is not equipped with the “model embedding” ΠMΘ →
Πμ(MΘ) ΠC(MΘ),
the “naively defined” action of ΠC(MΘ) on ΠMΘ|(l·ΔΘ)(MΘ) is in fact a
“natural action”inthesensethatitnecessarilycoincides withthenatural
conjugation action arising from this “model embedding”.
Next, let us observe that the inclusion ΔX(MΘ) ⊆ ΔX(MΘ) induces natural
isomorphisms
ΔX(MΘ)/ΔY (MΘ)∼
→ ΔX(MΘ)/ΔY (MΘ), Δell
Y (MΘ)∼
→ Δell
Y (MΘ)
of subquotients of ΠC(MΘ), whose codomains are [unlike the domains of these
isomorphisms!] stabilized by the conjugation action of ΠC(MΘ). In particular, by
applying these natural isomorphisms, one may regard the “commutator map”
of (iii) as a map
[−
,−] : (ΔX(MΘ)/ΔY (MΘ)) × Δell
Y (MΘ) → ΠMΘ|(l·ΔΘ)(MΘ)
— i.e., a map for which both the domain and the codomain are equipped with
natural actions by ΠC(MΘ). Now one verifies easily that this “commutator
map” is equivariant with respect to these natural actions by ΠC(MΘ), and,
24 SHINICHI MOCHIZUKI
moreover, that the various subgroups of ΠMΘ|(l·ΔΘ)(MΘ) constructed in (iii) are
stabilized by the natural action by ΠC(MΘ). In this context, it is also of in-
terest to note that, in fact, it follows immediately from a similar argument to
the argument concerning the automorphisms of a mono-theta environment given
in the proof of [EtTh], Corollary 2.18, (iv), that up to composition with auto-
morphisms of ΠMΘ that diﬀer from the identity automorphism by a twisted homo-
morphism ΠMΘ ΠY (MΘ) Πell
Y (MΘ) → Πμ(MΘ) that arises from a Kummer
¨
l
class of a product of integral powers of “(
U)2” and “q
2
X” [cf. [EtTh], Proposi-
tion 1.4, (ii)] — i.e., automorphisms that have no eﬀect on the construction of
the “commutator map” of the above display! — the “model embedding”
ΠMΘ → Πμ(MΘ) ΠC(MΘ) may be reconstructed algorithmically from the
mono-theta environment MΘ. Thus, in summary,
the various constructions discussed in (iii) that underlie the mono-theta-
theoretic cyclotomic rigidity isomorphism of Definition 1.1, (ii), are
stabilized by the natural action by ΠC(MΘ), hence, in particular, by the
natural action by (ΠC(MΘ) ⊇) ΔC(MΘ) ΔC(MΘ)/ΔX(MΘ)∼
= F ±
l.
Here, we remark that the fact that these constructions are stabilized by the ac-
tion of ΔX(MΘ) is “less interesting” in the sense that the automorphisms of
ΠX(MΘ) that arise from the conjugation action by ΔX(MΘ) lift [indeed, “almost
uniquely”! — cf. [EtTh], Corollary 2.18, (iv)] to automorphisms of MΘ, hence
stabilize the constructions under consideration as a consequence of the functoriality
of these constructions with respect to automorphisms [cf. [EtTh], Corollary 2.19,
(i)]. It is for this reason that, in the present context, it is natural to regard the
symmetry properties of interest as being symmetries with respect to the quotient
ΔC(MΘ) ΔC(MΘ)/ΔX(MΘ)∼
= F ±
l . On the other hand, the approach of the
above discussion via model embeddings to this full symmetry with respect to F ±
l
may also be regarded as being simply an explicit computation, in the case of this
F ±
l -symmetry, of the functoriality of the constructions under consideration with
respect to isomorphisms [cf. [EtTh], Corollary 2.19, (i)].
(v) In the context of the discussion following the final display of (iv), it is
perhaps of interest to recall that the symmetries of mono-theta environments
relative to the conjugation action by ΔX(MΘ) are a consequence of the “shift-
ing automorphisms” discussed in [EtTh], Proposition 2.14, (ii) [cf. the discussion
of [EtTh], Remark 2.14.3]. That is to say, despite the fact that the meromor-
phic function constituted by the theta function does not admit such symmetries,
the corresponding mono-theta environment does admit such symmetries. This
is one important diﬀerence between the theory of mono-theta environments and
the theory of bi-theta environments [cf. the discussion of [EtTh], Remark 2.14.3].
Alternatively, the existence of such symmetries may be regarded as
one of the fundamental diﬀerences between the mono-theta-theoretic
approach to cyclotomic rigidity taken in [EtTh] and the approach to
cyclotomic rigidity taken in [IUTchI], Example 5.1, (v), via Kummer
classes of rational functions.
Put another way, this fundamental diﬀerence may be thought of as the diﬀerence
between constructing a cyclotomic rigidity isomorphism from a line bundle—
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 25
i.e., which, in general, admits more symmetries than a rational function — and
constructing a cyclotomic rigidity isomorphism from a rational function. On the
other hand, if one attempts to mimick the approach of [EtTh] [i.e., of constructing
“shifting automorphisms” as in [EtTh], Proposition 2.14, (ii)] in the case of sym-
metries with respect to the quotient ΔC(MΘ) ΔC(MΘ)/ΔX(MΘ)∼
= F ±
l , then
it is necessary to allow “denominators of the form 1
” when one works with the
l
module ΠMΘ|(l·ΔΘ)(MΘ). In fact, however, when one computes the commutator map
[−
,−] considered in (iv), such terms with denominators vanish, as a consequence
of the fact that ΠMΘ|(l·ΔΘ)(MΘ) commutes with the elements of interest in the com-
putation of this commutator map. It is precisely this state of aﬀairs that allows
one to construct an F ±
l -symmetric cyclotomic rigidity isomorphism as dis-
cussed in (iv), that is to say, which, by itself, is somewhat weaker than the “full
mono-theta environment” [i.e., which does not admit F ±
l -symmetries unless one
allows for denominators as discussed above!]. Thus, in summary, by comparison to
the approach to cyclotomic rigidity taken in [EtTh], the slightly weaker approach
discussed in (iv) may be thought of as corresponding to the diﬀerence between con-
structing a cyclotomic rigidity isomorphism from a line bundle and constructing
a cyclotomic rigidity isomorphism from the curvature, or first Chern class, of
the line bundle [cf. the discussion of Remark 3.6.5 below].
One key property of mono-theta environments is that they may be constructed
either group-theoretically from Πtp
X
or category-theoretically from certain tempered
k
Frobenioids related to Xk.
Proposition 1.2. (Group- and Frobenioid-theoretic Constructions of
Mono-theta Environments)
(i) Let Π be a topological group isomorphic to Πtp
X
functorial group-theoretic algorithm
Π → MΘ(Π)
for constructing from the topological group Π a mod N mono-theta environ-
ment “up to isomorphism” [cf. [EtTh], Corollary 2.18, (ii)] such that the
composite of this algorithm with the algorithm MΘ(Π) → ΠX(MΘ(Π)) discussed in
Definition 1.1, (i), admits a functorial isomorphism Π∼
→ ΠX(MΘ(Π)). Here,
the “isomorphism indeterminacy” of MΘ(Π) is with respect to a group of “μN-
conjugacy classes” of automorphisms which is of order 1 (respectively, 2) if N is
odd (respectively, even) [cf. [EtTh], Corollary 2.18, (iv)].
(ii) Let C be a category equivalent to the tempered Frobenioid determined
by Xk [i.e., the Frobenioid denoted “C” in the discussion at the beginning of [EtTh],
§5; the Frobenioid denoted “F
v” in the discussion of [IUTchI], Example 3.2, (i)].
Thus, C admits a natural Frobenioid structure over a base category D equivalent
to Btemp(Πtp
X
)0 [cf. [FrdI], Corollary 4.11, (ii), (iv); [EtTh], Proposition 5.1].
k
Then there exists a functorial algorithm
C → MΘ(C)
. Then there exists a
k
26 SHINICHI MOCHIZUKI
for constructing from the category C a mod N mono-theta environment [cf.
[EtTh], Theorem 5.10, (iii)] such that the composite of this algorithm with the algo-
rithm MΘ(C) → ΠX(MΘ(C)) discussed in Definition 1.1, (i), admits a functorial
.
isomorphism D∼ → Btemp(ΠX(MΘ(C)))0
Proof. The assertions of Proposition 1.2 follow immediately from the results of
[EtTh] that are quoted in the statements of these assertions. ⃝
The cyclotomic rigidity isomorphism of Definition 1.1, (ii), that arises in the
case of the mono-theta environment MΘ(C) constructed from the tempered Frobe-
nioid C [cf. Proposition 1.2, (ii)] is compatible with a certain cyclotomic rigidity
isomorphism that arises in the theory of [AbsTopIII] [cf. also [FrdII], Theorem 2.4,
(ii)] in the following sense.
Proposition 1.3. (Compatibility of Cyclotomic Rigidity Isomorphisms)
In the situation of Proposition 1.2, (ii):
(i) (Mono-theta Environments Associated to Tempered Frobenioids)
For a suitable object S ∈ Ob(C) [cf. [EtTh], Lemma 5.9, (v)], whose image in D
we denote by Sbs ∈ Ob(D), the interior cyclotome (l· ΔΘ)(MΘ(C)) ⊗ (Z/NZ)
corresponds to a certain subquotient of Aut(Sbs), which we denote by (l·ΔΘ)S ⊗
(Z/NZ), while the exterior cyclotome Πμ(MΘ(C)) corresponds to the subgroup
μN(S) ⊆ O×(S) ⊆ Aut(S). In particular, the cyclotomic rigidity isomorphism
of Definition 1.1, (ii), takes the form of an isomorphism
(l·ΔΘ)S ⊗(Z/NZ)∼
→ μN(S) (∗mono-Θ)
[cf. [EtTh], Proposition 5.5; [EtTh], Lemma 5.9, (v)].
(ii) (MLF-Galois Pairs) Relative to the formal correspondence between p-
adic Frobenioids [such as the base-field-theoretic hull Cbs-fld associated to C
— cf. [EtTh], Definition 3.6, (iv)] and “MLF-Galois TM-pairs” in the theory
of [AbsTopIII] [cf. [AbsTopIII], Remark 3.1.1], “μN(S)” [cf. (i)] corresponds to
“μZ(MTM)⊗(Z/NZ)” in the theory of [AbsTopIII], §3 [cf. [AbsTopIII], Definition
3.1, (v)], while “(l·ΔΘ)S ⊗(Z/NZ)” [cf. (i)] corresponds to “μZ(ΠX)⊗(Z/NZ)”
in the theory of [AbsTopIII], §1 [cf. [AbsTopIII], Theorem 1.9, (b); [AbsTopIII],
Remark 1.10.1, (ii); [IUTchI], Remark 3.1.2, (iii)]. In particular, by composing the
inverse of the natural isomorphism “μZ(Gk)∼
→ μZ(ΠX)” of [AbsTopIII], Corollary
1.10, (c), with the inverse of the natural isomorphism “μZ(MTM)∼
→ μZ(G)” of [Ab-
sTopIII], Remark 3.2.1, we obtain another cyclotomic rigidity isomorphism
(l·ΔΘ)S ⊗(Z/NZ)∼
→ μN(S) (∗bs-Gal)
[cf. the various identifications/correspondences of notation discussed above].
(iii) (Compatibility) The cyclotomic rigidity isomorphisms (∗mono-Θ), (∗bs-Gal)
of [EtTh], [AbsTopIII] [cf. (i), (ii)] coincide.
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 27
Proof. Assertions (i), (ii) follow immediately from the results and definitions of
[EtTh], [AbsTopIII] that are quoted in the statements of these assertions. Assertion
(iii) follows immediately from the fact that in the situation where the Frobenioid
C involved is not just “some abstract category”, but rather arises from familiar ob-
jects of scheme theory [cf. the theory of [EtTh], §1!], both isomorphisms (∗mono-Θ),
(∗bs-Gal) coincide with the conventional identification between the cyclotomes in-
volved that arises from conventional scheme theory. ⃝
´
Proposition 1.4. (
Etale Theta Functions of Standard Type) Let Π be as
in Proposition 1.2, (i). Then there are functorial group-theoretic algorithms
[cf. [EtTh], Corollary 2.18, (i)]
Π → Π¨
Y (Π); Π → (l·ΔΘ)(Π)
for constructing from Π the open subgroup Π¨
Y (Π) ⊆ Π corresponding to the tem-
¨
pered covering “
Y” [cf. the discussion preceding [EtTh], Definition 2.7] and a cer-
tain subquotient (l·ΔΘ)(Π) of Π [cf. the subquotient “(l·ΔΘ)(MΘ)” of Definition
1.1, (i)], as well as a functorial group-theoretic algorithm
Π → θ(Π) ⊆ H1(Π¨
Y (Π),(l·ΔΘ)(Π))
— cf. the constant multiple rigidity property of [EtTh], Corollary 2.19, (iii)
— for constructing from Π the set θ(Π) of μl-multiples [i.e., where μl denotes the
group of l-th roots of unity] of the reciprocal of the “(l·Z×μ2)-orbit¨
ηΘ,l·Z×μ2 of
an l-th root of the´ etale theta function of standard type” of [EtTh], Definition
2.7. In this context, we shall write
∞θ(Π) ⊆ lim
− →J H1(Π¨
Y (Π)|J,(l·ΔΘ)(Π))
— where ∞θ(Π) denotes the subset of elements of the direct limit of cohomology
modules in the display for which some [positive integer] multiple [i.e., some [pos-
itive integer] power, if one writes these modules “multiplicatively”] coincides, up
to torsion, with an element of θ(Π); J ranges over the finite index open subgroups
of Π; the notation “|J” denotes the fiber product “×ΠJ”.
Proof. The assertions of Proposition 1.4 follow immediately from the results and
definitions of [EtTh] that are quoted in the statements of these assertions. ⃝
Remark 1.4.1. tion 1.4.
Before proceeding, let us recall from [EtTh], §1, §2, the theory
surrounding the“´ etale theta functions of standard type” that appeared in Proposi-
(i) Write
Xk → Xk → Ck
for the hyperbolic orbicurves of type (1,l-tors), (1,l-tors)± determined by Xk [cf.
[EtTh], Proposition 2.4]. Thus, Xk has a unique zero cusp [i.e., the unique cusp
fixed by the action of the Galois group Gal(Xk/Ck)]. Write
μ− ∈ Xk(k)
28 SHINICHI MOCHIZUKI
for the unique torsion point of order 2 whose closure in any stable model of Xk
over Ok intersects the same irreducible component of the special fiber of the stable
model as the zero cusp [cf. the discussion of [IUTchI], Example 4.4, (i)].
(ii) The unique order two automorphism ιX of Xk over k [cf. [EtTh], Remark
2.6.1] lies over an order two automorphism ιX [cf. [EtTh], Remark 2.6.1] and
corresponds at the level of tempered fundamental groups [cf., e.g., [SemiAnbd],
Theorem 6.4] to the unique order two Δtp
X
-outer automorphism of Πtp
X
over Gk,
k
k
which, by abuse of notation, we shall also denote by ιX. Write
¨
Yk → Yk → Xk
for the tempered coverings of Xk that correspond, respectively, to the open sub-
groups Πtp
¨
def = Π¨
Y
Y (Πtp
X
) ⊆ Πtp
X
[cf. Proposition 1.4], Πtp
Y
def = ΠY (Πtp
X
) def
=
k
k
k
k
k
ΠY (MΘ(Πtp
X
)) ⊆ Πtp
X
[cf. Definition 1.1, (i); Proposition 1.2, (i)]. Since k con-
k
k
tains a primitive 4l-th root of unity, it follows from the definition of an “´ etale theta
function of standard type” [cf. [EtTh], Definition 1.9, (ii); [EtTh], Definition 2.7]
that there exist rational points
(μ−)¨
Y ∈¨
Yk(k), (μ−)X ∈ Xk(k)
such that (μ−)¨
Y → (μ−)X → μ−. Since ιX fixes μ−, it follows immediately that
ιX fixes the Gal(Xk/Xk)-orbit of (μ−)X, hence [since Aut(Xk)∼
= Z/2lZ, where we
recall that l ̸= 2 — cf. [EtTh], Remark 2.6.1] that ιX fixes (μ−)X. One verifies
immediately that this implies that there exists an order two automorphism ι¨
Y of
¨
Yk lifting ιX which is uniquely determined up to l· Z-conjugacy and composition
¨
¨
with an element ∈ Gal(
Yk/Yk) by the condition that it fix the Gal(
Yk/Yk)-orbit of
some element [which, by abuse of notation, we shall continue to denote by “(μ−)¨
Y ”]
¨
¨
of the Gal(
Yk/Xk)-orbit of (μ−)¨
Y . Here, we think of l·Z, Gal(
Yk/Yk) (∼
= Z/2Z)
as the subquotients appearing in the natural exact sequence
¨
¨
1 → Gal(
Yk/Yk) → Gal(
Yk/Xk) → l·Z → 1
¨
determined by the coverings
Yk → Yk → Xk. Again, by abuse of notation, we
shall also denote by ι¨
Y the corresponding Δtp
¨
Y
(= Δtp
X
k
k
Πtp
¨
Y
)-outer automor-
k
phism of Πtp
¨
. We shall refer to the various automorphisms ιX, ι¨
Y
Y as inversion
k
automorphisms [cf. [EtTh], Proposition 1.5, (iii)]. Write
Dμ− ⊆ Π¨
Y
k
for the decomposition group of (μ−)¨
Y [which is well-defined up to Δtp
¨
Y
-conjugacy]
k
— so Dμ− is determined by ι¨
Y up to Δtp
Yk (def = ΔY (MΘ(Πtp
X
)))-conjugacy [cf. the
k
notation of Remark 1.1.1, (i)]. We shall refer to either of the pairs
¨
(ι¨
Y ∈ Aut(
Yk),(μ−)¨
Y ); (ι¨
Y ∈ Aut(Πtp
¨
Y
)/Inn(Δtp
¨
Y
),Dμ−)k
k
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 29
as a pointed inversion automorphism. Again, we recall from [EtTh], Definition
1.9, (ii); [EtTh], Definition 2.7, that
an “´ etale theta function of standard type” is defined precisely by the con-
dition that its restriction to Dμ−
be a 2l-th root of unity.
Proposition 1.5. (Projective Systems of Mono-theta Environments) In
the notation of the above discussion, let
MΘ
∗
= {... → MΘ
M′ → MΘ
M →...}
be a projective system of mono-theta environments — where MΘ
M is a mod
M mono-theta environment [which is isomorphic to the mod M model mono-theta
environment determined by Xk], and the index M of the projective system varies
multiplicatively among the elements of N≥1 [cf. [EtTh], Corollary 2.19, (ii),
(iii)]. Then:
(i) Such a projective system is uniquely determined, up to isomorphism,
by Xk [cf. Remark 1.5.1 below; the discrete rigidity property of [EtTh], Corollary
2.19, (ii)].
(ii) The transition morphisms of the resulting projective system of topological
groups {... → ΠX(MΘ
M′) → ΠX(MΘ
M) →...} [cf. the notation of Definition
1.1, (i)] are all isomorphisms. Moreover, any isomorphism of topological groups
ΠX(MΘ
M′)∼
→ ΠX(MΘ
M), where M divides M′
, lifts to a morphism of mono-theta
environments MΘ
M′ → MΘ
M [cf. [EtTh], Corollary 2.18, (iv)]. Thus, to simplify the
notation, we shall identify these topological groups via these transition morphisms
and denote the resulting topological group by the notation ΠX(MΘ
∗ ). In particular,
we have an open subgroup Π¨
Y (MΘ
∗ ) ⊆ ΠX(MΘ
∗ ), a subquotient (l·ΔΘ)(MΘ
∗ ) of
ΠX(MΘ
∗ ), and a quotient ΠX(MΘ
∗ ) G(MΘ
∗ ) [cf. Definition 1.1, (i); Proposition
1.4].
(iii) The projective system of exterior cyclotomes {... → Πμ(MΘ
M′) →
Πμ(MΘ
M) →...} [cf. the notation of Definition 1.1, (i)] determines a projective
limit exterior cyclotome Πμ(MΘ
∗ ) which is equipped with a uniquely determined
cyclotomic rigidity isomorphism
(l·ΔΘ)(MΘ
∗ )∼
→ Πμ(MΘ
∗ )
[i.e., obtained by applying the cyclotomic rigidity isomorphisms of Definition 1.1,
(ii), to the various members of the projective system MΘ
∗ ]. In particular, [cf. Propo-
sition 1.4] we obtain a functorial algorithm
MΘ
∗ → θ
env(MΘ
∗ ) ⊆ H1(Π¨
Y (MΘ
∗ ),Πμ(MΘ
∗ ))
— where one may think of the “env” as an abbreviation of the term “[mono-theta]
environment” — for constructing from MΘ
∗ an exterior cyclotome version
30 SHINICHI MOCHIZUKI
θ
env(MΘ
∗ ) of θ(Π) [i.e., by transporting θ(Π) via the above cyclotomic rigidity iso-
morphism] — cf. [EtTh], Corollary 2.19, (iii). In this context, we shall write
∞θ
env(MΘ
∗ ) ⊆ lim
− →
J
H1(Π¨
Y (MΘ
∗ )|J,Πμ(MΘ
∗ ))
— where ∞θ
env(MΘ
∗ ) denotes the subset of elements of the direct limit of cohomol-
ogy modules in the display for which some [positive integer] multiple [i.e., some
[positive integer] power, if one writes these modules “multiplicatively”] coincides,
up to torsion, with an element of θ
env(MΘ
∗ ); J ranges over the finite index open
subgroups of ΠX(MΘ
∗ ).
(iv) Suppose that MΘ
∗ arises from a tempered Frobenioid C [cf. Propositions
1.2, (ii); 1.3]. Then this construction of θ
env(MΘ
∗ ) [cf. (iii)] is compatible with
the Kummer-theoretic construction of the ´ etale theta function — i.e., by con-
sidering Galois actions on roots of the Frobenioid-theoretic theta function [cf.
the theory of [EtTh], §5]. In particular, it is compatible with the Kummer theory
of the base-field-theoretic hull Cbs-fld [cf. [FrdII], Theorem 2.4; [AbsTopIII],
Proposition 3.2, (ii); [AbsTopIII], Remark 3.1.1].
Proof. The assertions of Proposition 1.5 follow immediately from the results and
definitions of [EtTh] [as well as [FrdII], [AbsTopIII]] that are quoted in the state-
ments of these assertions. ⃝
Remark 1.5.1. We recall in passing that one important consequence of the
discrete rigidity property established in [EtTh], Corollary 2.19, (ii) — which, in
eﬀect, allows one to restrict one’s attention to l· Z-translates [i.e., as opposed
to l· Z-translates] of the usual theta function — is the resulting compatibility of
projective systems of mono-theta environments [as in Proposition 1.5] with the
discrete structure inherent in the various isomorphs of the monoid N that appear
in the structure of the tempered Frobenioids that arise in the theory [cf. [EtTh],
Remark 2.19.4; [EtTh], Remark 5.10.4, (i), (ii)].
Remark 1.5.2. Note that, in the notation of Proposition 1.5, (iii), by consider-
ing “tautological Kummer classes” of elements of Πμ(MΘ
∗ ), one obtains a natural
ΠX(MΘ
∗ )-equivariant injection
Πμ(MΘ
∗ ) ⊗ Q/Z → lim
− →
J
H1(Π¨
Y (MΘ
∗ )|J,Πμ(MΘ
∗ ))
whose image is equal to the torsion subgroup of the codomain of the injection.
Indeed, it follows immediately from the fact that Πμ(MΘ
∗ ) is torsion-free that the
torsion subgroup of the codomain of the displayed injection may be identified with
the torsion subgroup of
lim
− →
H1(JG,Πμ(MΘ
∗ ))
J
— where J ranges over the finite index open subgroups of ΠX(MΘ
∗ ); we write JG for
the image of J in G(MΘ
∗ ). The desired conclusion thus follows immediately from
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 31
the well-known Kummer theory of MLF’s, i.e., the fact that the Kummer map
(Πμ(MΘ
∗ ) ⊗ Q/Z)J → H1(JG,Πμ(MΘ
∗ )) [where the superscript “J” denotes the
submodule of J-invariants] is injective with image equal to the torsion subgroup of
the codomain.
Before proceeding, we review a certain portion of the theory of [AbsTopII] that
is relevant to the content of the present §1.
Proposition 1.6. (Cores and Cuspidalizations) Let Π be as in Proposition
1.2, (i). Write Δ ⊆ Π for the [group-theoretic! — cf., e.g., [AbsAnab], Lemma
1.3.8] subgroup corresponding to Δtp
. Then:
X
k
(i) (Cores) There exists a functorial group-theoretic algorithm [cf. [Ab-
sTopII], Corollary 3.3, (i); [AbsTopII], Remark 3.3.3]
Π → (Π ⊆) ΠC(Π) Π/Δ
for constructing from Π a topological group ΠC(Π) equipped with an augmentation
[i.e., a surjection] ΠC(Π) Π/Δ — whose kernel we denote by ΔC(Π) — that
contains Π as an open subgroup in a fashion that is compatible with the respec-
tive surjections to Π/Δ and which satisfies the property that when Π = Πtp
X
, the
k
inclusion Π ⊆ ΠC(Π) may be naturally identified with the inclusion Πtp
X
⊆ Πtp
Ck.
k
(ii) (Elliptic Cuspidalizations) Let N be a positive integer. Then there
exists a functorial group-theoretic algorithm [cf. [AbsTopII], Corollary 3.3,
(iii); [AbsTopII], Remark 3.3.3]
Π → ΠUN (Π) Π
for constructing from Π a topological group ΠUN (Π) equipped with a surjection
ΠUN (Π) Π [so the augmentation Π Π/Δ determines, by composition, an aug-
mentation ΠUN (Π) Π/Δ] such that when Π = Πtp
X
, the surjection ΠUN (Π) Π
k
may be naturally identified with a certain surjection — i.e., “elliptic cuspidaliza-
tion” — that arises from a certain open immersion determined by the N-torsion
points of a once-punctured elliptic curve that forms a double covering of Ck [cf.
[AbsTopII], Corollary 3.3, (iii)].
Proof. The assertions of Proposition 1.6 follow immediately from the results of
[AbsTopII] that are quoted in the statements of these assertions [cf. also Remark
1.6.1 below]. ⃝
Remark 1.6.1. We recall in passing that the construction of Proposition 1.6,
(i), amounts, in eﬀect, to the computation of various centralizers of the image of
various open subgroups of Π/Δ in the outer automorphism groups of various open
subgroups of Δ. In a similar vein, the construction of Proposition 1.6, (ii), amounts
to the computation of various outer isomorphisms between various subquotients of
32 SHINICHI MOCHIZUKI
Δ that are compatible with the outer actions of various open subgroups of Π/Δ.
More generally, although in Proposition 1.6, we restricted our attention to the con-
struction of cores and elliptic cuspidalizations, an analogous result may be obtained
for more general functorial group-theoretic algorithms involving “chains of elemen-
tary operations”, as discussed in [AbsTopI], §4 — e.g., for Belyi cuspidalizations,
as discussed in [AbsTopII], Corollary 3.7.
Next, we proceed to discuss the “multiradial” interpretation of the theory of
[EtTh] that is of interest in the context of the present series of papers. We begin
by examining various examples of the sort of situation that gives rise to such an
interpretation.
Example 1.7. Radial and Coric Data I: Generalities.
(i) In the following discussion, we would like to consider a certain “type of
mathematical data”, which we shall refer to as radial data. This notion of a “type
of mathematical data” may be formalized — cf. [IUTchIV], §3, for more details.
From the point of view of the present discussion, one may think of a “type of
mathematical data” as the input or output data of a “functorial algorithm” [cf. the
discussion of [IUTchI], Remark 3.2.1]. At a more concrete level, we shall assume
that this “type of mathematical data” gives rise to a category
R
— i.e., each of whose objects is a specific collection of radial data, and each of whose
morphisms is an isomorphism. In the following discussion, we shall also consider
another “type of mathematical data”, which we shall refer to as coric data. Write
C
for the category obtained by considering specific collections of coric data and iso-
morphisms of collections of coric data. In addition, we shall assume that we are
given a functorial algorithm — which we shall refer to as radial — whose input data
consists of a collection of radial data, and whose output data consists of a collection
of coric data. Thus, this functorial algorithm gives rise to a functor Φ : R → C. In
the following discussion, we shall assume that this functor is essentially surjective.
We shall refer to the category R and the functor Φ as radial and to the category
C as coric. Finally, if I is some nonempty index set, then we shall often consider
collections
{Φi : Ri → C}i∈I
of copies of Φ and R, such that the various copies of Φ have the same codomain C
— cf. Fig. 1.1 below. Thus, one may think of each Ri as the category of radial
data equipped with a label i ∈ I, and isomorphisms of such data.
(ii) We shall refer to a triple (R,C,Φ : R → C) [or to the triple consisting of
the corresponding “types of mathematical objects” and “functorial algorithm”] of
the sort discussed in (i) as a radial environment. If Φ is full, then we shall refer
to the radial environment under consideration as multiradial. We shall refer to a
radial environment which is not multiradial as uniradial. Suppose that the radial
environment (R,C,Φ : R → C) under consideration is uniradial. Then an object of
R may, in general, lose a certain portion of its rigidity — i.e., may be subject to a
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 33
certain additional indeterminacy — when it is mapped to C. Put another way,
in general, an object of C is imparted with a certain additional rigidity — i.e.,
loses a certain portion of its indeterminacy — when one fixes a lifting of the object
to R. Thus, in summary,
the condition that (R,C,Φ : R → C) be multiradial may be thought of as
a condition to the eﬀect that the application of the radial algorithm does
not result in any loss of rigidity.
Finally, we observe that, if (R,C,Φ : R → C) is an arbitrary radial environment
such that any two collections of radial data are isomorphic, then one may define
the associated [tautological] multiradialization
(Rmtz
,C,Φmtz : Rmtz → C)
of this radial environment as follows: A collection of radial data
(R,C,α)
of this multiradialization consists of an object R of R, an object C of C, and the full
poly-isomorphism [cf. [IUTchI], §0] α : Φ(R)∼
→ C. An isomorphism of collections
of radial data (R,C,α)∼
→ (R∗,C∗,α∗) of the multiradialization consists of a pair of
isomorphisms R∼
→ R∗
, C∼
→ C∗ [which are necessarily compatible with α, α∗]. The
coric data of the multiradialization is taken to be the coric data of the original radial
environment (R,C,Φ : R → C). The radial algorithm of the multiradialization is
taken to be the assignment
(R,C,α) → C
— whose associated radial functor is clearly full [cf. our assumption that any
two collections of radial data are isomorphic!] and essentially surjective, hence
determines a [tautologically!] multiradial environment (Rmtz
,C,Φmtz : Rmtz → C),
together with a natural functor R → Rmtz [i.e., given by the assignment R →
(R,Φ(R),Φ(R)∼
→ Φ(R))]. Indeed,
the tautological multiradialization of the given radial environment
may be thought of as the result of “forgetting, in a minimal possible fash-
ion, the uniradiality” of the original radial environment (R,C,Φ : R → C).
Ri
...
⏐ ⏐...
Ri′ −→ C ←− Ri′′
... ⏐ ⏐...
Ri′′′
Fig. 1.1: Radial functors valued in a single coric category
34 SHINICHI MOCHIZUKI
(iii) In passing, we pause to observe that one way to think of the significance
of the multiradiality of a radial environment (R,C,Φ : R → C) is as follows: Write
R×C R
for the category whose objects are triples (R1,R2,α) consisting of a pair of objects
R1, R2 of R and an isomorphism α : Φ(R1)∼
→ Φ(R2) between the images of R1,
R2 via Φ, and whose morphisms are the morphisms [in the evident sense] between
such triples [cf. the discussion of the “categorical fiber product” given in [FrdI], §0].
Write sw : R×C R∼ → R×C R for the functor (R1,R2,α) → (R2,R1,α−1) obtained
by switching the two factors of R. Then
one formal consequence of the multiradiality of a radial environment
(R,C,Φ : R → C) is the property that the switching functor sw :
R×CR∼ → R×CR preserves the isomorphism class of objects of R×CR.
Indeed, one verifies immediately that this multiradiality is, in fact, equivalent to
the condition that every object (R1,R2,α) of R×C R be isomorphic to the object
(R1,R1,id : Φ(R1)∼
→ Φ(R1)) [which is manifestly left unchanged by the switching
functor].
(iv) Next, suppose that we are given another radial environment (R†
,C†
,Φ† :
R† → C†). We shall refer to the “type of mathematical object”/“functorial algo-
rithm” that gives rise to R† (respectively, C†; Φ†) as daggered radial data (respec-
tively, daggered coric data; the daggered radial functorial algorithm). Also, let us
suppose that we are given a 1-commutative diagram
R ΨR −→ R†
⏐ ⏐Φ
⏐ ⏐Φ†
C ΨC −→ C†
— where ΨR and ΨC arise from “functorial algorithms”. If (R,C,Φ : R → C)
is multiradial (respectively, uniradial), then we shall refer to ΨR as multiradially
defined (respectively, uniradially defined), or [when there is no fear of confusion
between Φ and ΨR] as multiradial (respectively, uniradial). If ΨR admits a 1-
factorization ΞR ◦Φ for some ΞR : C → R† that arises from a functorial algorithm,
then we shall say that ΨR is corically defined, or [when there is no fear of
confusion] coric. Thus, by considering the case where R= C, Φ = idR, one may
think of the notion of a corically defined ΨR as a sort of special case of the notion
of a multiradial ΨR.
(v) Suppose that we are in the situation of (iv), and that ΨR is multiradially
defined. Then one way to think of the significance of the multiradiality of ΨR is
as follows:
ThemultiradialityofΨR rendersitpossibletoconsiderthesimultaneous
execution of the functorial algorithm corresponding to ΨR relative to
various collections of radial input data indexed by the set I [cf. Fig.
1.1] in a fashion that is compatible with the identification of the coric
portions [i.e., corresponding to Φ] of these collections of radial input data
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 35
— cf. Remark 1.9.1 below for more on this point of view. That is to say, at a more
technical level, if one implements this identification of the various coric portions by
means of various gluing isomorphisms in C, then the multiradiality of ΨR implies
that one may lift these gluing isomorphisms in C to gluing isomorphisms in R; one
may then apply ΨR to these gluing isomorphisms in R to obtain gluing isomor-
phisms of the output data of ΨR. Put another way, if one assumes instead that
ΨR is uniradial, then the output data of ΨR depends, a priori, on the “additional
rigidity” [cf. (ii)] of objects of R relative to these images in C; thus, if one attempts
to identify these images in C via arbitrary gluing isomorphisms in C, then one does
not have any way to compute the eﬀect of such gluing isomorphisms on the output
data of ΨR.
Remark 1.7.1. One way to understand the significance of the fullness condi-
tion in the definition of a multiradial environment is as a condition that allows
one to execute a sort of parallel transport operation between “fibers” of the ra-
dial functor Φ : R → C [cf. the notation of Example 1.7, (iv)] — i.e., by lifting
isomorphisms in C to isomorphisms in R [cf. the discussion of Example 1.7, (v)].
Here, it is perhaps of interest to make the tautological observation that, up to an
indeterminacy arising from the extent that Φ fails to be faithful, such liftings are
unique. That is to say, whereas a uniradial environment may be thought of as
a sort of abstraction of the geometric notion of a“fibration that is not equipped
with a connection”,
a multiradial environment may be thought of as a sort of abstraction
of the geometric notion of a “fibration equipped with a connection”
—
i.e., that allows one to execute parallel transport operations between the
“fibers”.
Relative to this point of view, one may think of the coric data as the portion of
the radial data of a multiradial environment that is horizontal with respect to the
“connection structure”. We refer to Remarks 1.9.1, 1.9.2 below for more on the
significance of multiradiality.
Example 1.8. Radial and Coric Data II: Concrete Examples. In this
following, we consider various concrete examples of multiradial environments, many
of which may, in fact, be understood as special cases of the notion of the tautological
multiradialization associated to a suitable choice of radial environment, i.e., as
discussed in Example 1.7, (ii).
(i) From the point of view of the theory to be developed in the remainder of the
present §1, perhaps the most basic example of a radial environment is the following.
We define a collection of radial data
(Π,G,α)
to consist of a topological group Π isomorphic to Πtp
X
, a topological group G iso-
k
morphic to Gk, and the full poly-isomorphism [cf. [IUTchI], §0] of topological
groups α : Π/Δ∼
→ G, where we write Δ ⊆ Π for the [group-theoretic! — cf.,
e.g., [AbsAnab], Lemma 1.3.8] subgroup corresponding to Δtp
X
. An isomorphismk
36 SHINICHI MOCHIZUKI
of collections of radial data (Π,G,α)∼
→ (Π∗,G∗,α∗) is defined to be a pair of
isomorphisms of topological groups Π∼
→ Π∗
, G∼
→ G∗ [which are necessarily com-
patible with α, α∗!]. A collection of coric data is defined to be a topological group
isomorphic to Gk; an isomorphism of collections of coric data is defined to be an
isomorphism of topological groups. The radial algorithm is the algorithm given
by the assignment
(Π,G,α) → G
—whoseassociatedradialfunctorisfullandessentially surjective,hencedetermines
a multiradial environment. Note that this example may be thought of as a sort of
formalization in the present context of the situation depicted in [IUTchI], Fig. 3.2,
at v ∈ Vbad — cf. Fig. 1.2 below. Here, we recall that the topological group
“G” [which is isomorphic to Gk] that appears in the center of Fig. 1.2 is regarded
as being known only up to isomorphism, and that the various isomorphs of ΠX
k
that appear in the “spokes” of Fig. 1.2 may be regarded as various “arithmetic
holomorphic structures” on “G” [cf. [IUTchI], Remark 3.8.1, (iii)].
iΠ
...
⏐ ⏐...
i′
Π −→ G ←− i′′
Π
... ⏐ ⏐...
i′′′
Π
Fig. 1.2: Diﬀerent arithmetic holomorphic structures on a single coric G
(ii) Recall the functorial group-theoretic algorithm
Π → (Π MTM(Π)) (∗TM)
of [AbsTopIII], §3 [cf., especially, the functors κAn, φAn of [AbsTopIII], Definition
3.1, (vi); [AbsTopIII], Corollary 3.6, (ii); [IUTchI], Remark 3.1.2] that assigns to
a topological group Π isomorphic to Πtp
X
an MLF-Galois TM-pair, which we shall
k
denote Π MTM(Π), and which is isomorphic to the “model” MLF-Galois TM-
pair determined by the natural action of Πtp
X
on the ind-topological monoid O◃
. In
k
k
fact, [the union with {0} of] the underlying ind-topological monoid MTM(Π) is also
equipped with a natural ring structure [cf. [AbsTopIII], Proposition 3.2, (iii)]. On
the other hand, if one is willing to sacrifice this ring structure, then there exists a
functorial group-theoretic algorithm
G → (G O◃(G)) (∗◃)
[cf. [AbsTopIII], Proposition 5.8, (i)] that assigns to a topological group G isomor-
phic to Gk an MLF-Galois TM-pair, which we shall denote G O◃(G), and which
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 37
is isomorphic to the MLF-Galois TM-pair determined by the natural action of Gk
on the ind-topological monoid O◃
k . Moreover, by [AbsTopIII], Proposition 3.2, (iv)
[cf. also Remark 1.11.1, (i), (a), below], there is a [uniquely determined] functorial
tautological isomorphism of MLF-Galois TM-pairs
(Π MTM(Π))∼
→ (Π/Δ O◃(Π/Δ))|Π (∗TM◃)
— where Δ ⊆ Π is as in (i), and the notation “|Π” denotes the restriction of the
action of Π/Δ to an action of Π. Then another important example of a radial
environment is the following. We define a collection of radial data
(Π MTM(Π),G O◃(G),α◃)
to consist of the output data of the algorithm (∗TM) associated to a topological
group Π isomorphic to Πtp
X
, the output data of the algorithm (∗◃) associated to a
k
topological group G isomorphic to Gk, and the poly-isomorphism [cf. [IUTchI], §0]
of MLF-Galois TM-pairs
α◃ : (Π MTM(Π))∼
→ (G O◃(G))|Π
determined [in light of [AbsTopIII], Proposition 3.2, (iv)] by the composite of the
natural surjection Π Π/Δ with the full poly-isomorphism of topological groups
Π/Δ∼
→ G [where Δ ⊆ Π is as in (i)]. An isomorphism of collections of radial data
(Π MTM(Π),G O◃(G),α◃)∼
→ (Π∗ MTM(Π∗),G∗ O◃(G∗),α∗
◃) is de-
finedtobeapairofisomorphismsofMLF-GaloisTM-pairs(Π MTM(Π))∼
→(Π∗
MTM(Π∗)), (G O◃(G))∼
→ (G∗ O◃(G∗)) [which are necessarily compatible
with α◃, α∗
◃!]. A collection of coric data is defined to be the output data of the
algorithm (∗◃) for some topological group isomorphic to Gk; an isomorphism of
collections of coric data is defined to be the isomorphism between collections of
output data of (∗◃) associated to an isomorphism of topological groups. The ra-
dial algorithm is the algorithm given by the assignment
(Π MTM(Π),G O◃(G),α◃) → (G O◃(G))
—whoseassociatedradialfunctorisfullandessentially surjective,hencedetermines
a multiradial environment.
(iii) Let
Γ ⊆ Z×
be a closed subgroup [cf. Remark 1.11.1, (i), (ii), below, for more on the significance
of Γ]. Then by considering the subgroups of invertible elements of the various ind-
topological monoids that appeared in (ii), one obtains functorial group-theoretic
algorithms
Π → (Π M×
TM(Π)); G → (G O×(G)) (∗×)
defined, respectively, on topological groups Π isomorphic to Πtp
X
and G isomorphic
k
to Gk. Here, we note that we may think of Γ as acting on the output data of the
38 SHINICHI MOCHIZUKI
second algorithm of (∗×) by means of the trivial action on G and the natural action
of Z× on O×(G). Then one obtains another example of a radial environment as
follows. We define a collection of radial data
(Π M×
TM(Π),G O×(G),α×)
to consist of the output data of the first algorithm of (∗×) associated to a topolog-
ical group Π isomorphic to Πtp
X
, the output data of the second algorithm of (∗×)
k
associated to a topological group G isomorphic to Gk, and the poly-isomorphism [cf.
[IUTchI], §0] of ind-topological modules equipped with topological group actions
α× : (Π M×
TM(Π))∼
→ (G O×(G))|Π
determined by the Γ-orbit of the poly-isomorphism “α◃|×” induced by the poly-
isomorphismα◃ of(ii). Anisomorphism of collections of radial data(Π M×
TM(Π),
G O×(G),α×)∼
→ (Π∗ M×
TM(Π∗),G∗ O×(G∗),α∗
×) is defined to consist of
theisomorphismofind-topologicalmodulesequippedwithtopologicalgroupactions
(Π M×
TM(Π))∼
→ (Π∗ M×
TM(Π∗)) induced by an isomorphism of topological
groups Π∼
→ Π∗, together with a Γ-multiple of the isomorphism of ind-topological
modulesequippedwithtopologicalgroupactions(G O×(G))∼
→(G∗ O×(G∗))
induced by an isomorphism of topological groups G∼
→ G∗ [so one verifies immedi-
ately that these isomorphisms are compatible with α×, α∗
× in the evident sense]. A
collection of coric data is defined to be the output data of the second algorithm of
(∗×) for some topological group isomorphic to Gk; an isomorphism of collections
of coric data is defined to be a Γ-multiple of the isomorphism between collections
of output data of (∗×) associated to an isomorphism of topological groups. The
radial algorithm is the algorithm given by the assignment
(Π M×
TM(Π),G O×(G),α×) → (G O×(G))
—whoseassociatedradialfunctorisfullandessentially surjective,hencedetermines
a multiradial environment.
(iv) By considering the subgroups of torsion elements of the various ind-topo-
logical monoids that appeared in (ii) and (iii), one obtains functorial group-theoretic
algorithms
Π → (Π Mμ
TM(Π)); G → (G Oμ(G)) (∗μ)
defined, respectively, on topological groups Π isomorphic to Πtp
and G isomor-
X
k
phic to Gk — i.e., a “cyclotomic version” of the algorithms of (∗×) [cf. (iii)].
Moreover, by forming the quotients M×μ
TM (−) def
= M×
TM(−)/Mμ
TM(−), O×μ(−) def
=
O×(−)/Oμ(−), one obtains functorial group-theoretic algorithms
Π → (Π M×μ
TM (Π)); G → (G O×μ(G)) (∗×μ)
defined, respectively, on topological groups Π isomorphic to Πtp
X
and G isomorphic
k
to Gk — i.e., a “co-cyclotomic version” of the algorithms of (∗×) [cf. (iii)]. Now
one verifies easily that
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 39
by replacing the symbol “×” in (iii) by the symbol “μ” or, alternatively,
by the symbol “×μ”,
one obtains, respectively, “cyclotomic” and “co-cyclotomic” versions of the example
treated in (iii). In the case of “×μ”, let us write
Ism(G)
for the compact topological group of G-isometries of O×μ(G), i.e., G-equivariant
automorphisms of the ind-topological moduleO×μ(G) that, for each open subgroup
H ⊆ G, preserve the “lattice” in O×μ(G)H determined by the image of O×(G)H
[i.e., where the superscript “H” denotes the submodule of H-invariants]. Let
Γ×μ ⊆ Ism(−)
be a closed subgroup, i.e., a collection of closed subgroups of each Ism(G) that is
∼
preserved by arbitrary isomorphisms of topological groups G1
→ G2. Then one
verifies easily that, in the “co-cyclotomic” version discussed above of the example
treated in (iii),
one may replace the “Γ” in (iii) by such a “Γ×μ”.
Finally, we observe that one example of such a “Γ×μ” — which we shall denote by
means of the notation
Ism
— is the case where one takes Γ×μ to be the entire group “Ism(−)”; another
example of such a “Γ×μ” is the image Im(Z×) of the natural homomorphism Z×
Z×
p → Ism.
(v) Another example of a radial environment may be obtained as follows. We
define a collection of radial data
(Π Mμ
TM(Π),G O×μ(G),αμ,×μ)
to consist of the output data of the first algorithm of (∗μ) associated to a topological
group Π isomorphic to Πtp
X
, the output data of the second algorithm of (∗×μ)
k
associated to a topological group G isomorphic to Gk, and the poly-morphism [cf.
[IUTchI], §0] of ind-topological modules equipped with topological group actions
αμ,×μ : (Π Mμ
TM(Π)) → (G O×μ(G))|Π
determined by the full poly-isomorphism Π/Δ∼
→ G [cf. (i)] and the trivial ho-
momorphism Mμ
TM(Π) → O×μ(G) — i.e., the composite of the natural homomor-
phisms Mμ
TM(Π) ⊆ M×
TM(Π)∼ → O×(G) O×μ(G) [where the “∼
→ ” arises from
the poly-isomorphism α× of (iii)]. An isomorphism of collections of radial data
(Π Mμ
TM(Π),G O×μ(G),αμ,×μ)∼
→ (Π∗ Mμ
TM(Π∗),G∗ O×μ(G∗),α∗
μ,×μ)
is defined to consist of the isomorphism of ind-topological modules equipped with
topological group actions (Π Mμ
TM(Π))∼
→ (Π∗ Mμ
TM(Π∗)) induced by an
isomorphism of topological groups Π∼
→ Π∗, together with a Γ×μ-multiple of the
isomorphism of ind-topological modules equipped with topological group actions
40 SHINICHI MOCHIZUKI
(G O×μ(G))∼
→ (G∗ O×μ(G∗)) induced by an isomorphism of topological
groups G∼
→ G∗ [so one verifies immediately that these isomorphisms are compat-
ible with αμ,×μ, α∗
μ,×μ in the evident sense]. A collection of coric data is defined
to be the output data of the second algorithm of (∗×μ) for some topological group
isomorphic to Gk; an isomorphism of collections of coric data is defined to be a
Γ×μ-multiple of the isomorphism between collections of output data of (∗×μ) asso-
ciated to an isomorphism of topological groups. [That is to say, the definition of
the coric data is the same as in the “co-cyclotomic” version discussed in (iv).] The
radial algorithm is the algorithm given by the assignment
(Π Mμ
TM(Π),G O×μ(G),αμ,×μ) → (G O×μ(G))
—whoseassociatedradialfunctorisfullandessentially surjective,hencedetermines
a multiradial environment.
(vi) By replacing the notation “Mμ
TM(Π)” in the discussion of (v) by the no-
tation “Πμ(MΘ
∗ (Π)) ⊗ Q/Z” [cf. Propositions 1.2, (i); 1.5, (i), (iii)], one verifies
immediately that one obtains an “exterior-cyclotomic version” of the multiradial
environment constructed in (v).
(vii) In the discussion to follow, we shall also consider the functorial group-
theoretic algorithms
Π → (Π Mgp
TM(Π)); G → (G Ogp(G)) (∗gp)
obtained by passing to the respective groupifications of the monoids MTM(Π),
O◃(G), as well as the functorial group-theoretic algorithms
Π → (Π Mgp
TM(Π)); G → (G Ogp(G)) (∗
gp)
obtained by passing to the respective inductive limits of the profinite completions
of Mgp
TM(Π)J
, Ogp(G)J [i.e., where the superscript “J” denotes the submodule of J-
invariants], as J ranges over the open subgroups of Π or G. Thus, there is a natural
action of Γ on the underlying ind-topological modules of Mgp
TM(Π), Ogp(G); by
considering the Γ-orbit of the poly-isomorphism induced by the poly-isomorphism
α◃ of (ii), one obtains a poly-isomorphism
α
gp : (Π Mgp
TM(Π))∼
→ (G Ogp(G))|Π
that is compatible [in the evident sense] with the poly-isomorphism α× of (iii).
(viii) The following example of a radial environment is another variant of the
example of (iii). We define a collection of radial data
(Π MTM(Π),G Ogp(G),α◃,×μ)
to consist of the output data of the algorithm of (∗TM) associated to a topologi-
cal group Π isomorphic to Πtp
X
, the output data of the second algorithm of (∗
gp)k
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 41
[cf. (vii)] associated to a topological group G isomorphic to Gk, and the follow-
ing diagram α◃,×μ of poly-morphisms of ind-topological monoids equipped with
topological group actions
(Π MTM(Π)) → (Π Mgp
TM(Π))
∼
→ (G Ogp(G))|Π ← (G O×(G))|Π
(G O×μ(G))|Π
— where the “ → ” denotes the natural inclusion; the “∼
→ ” denotes the poly-
isomorphism α
gp of (vii); the “ ← ” denotes the natural inclusion; the “ ”
denotes the natural surjection. An isomorphism of collections of radial data (Π
MTM(Π),G Ogp(G),α◃,×μ)∼
→ (Π∗ MTM(Π∗),G∗ Ogp(G∗),α∗
◃,×μ) is
defined to consist of the isomorphism of ind-topological monoids equipped with
topological group actions (Π MTM(Π))∼
→ (Π∗ MTM(Π∗)) induced by an
isomorphism of topological groups Π∼
→ Π∗, together with a Γ-multiple of the
isomorphism of ind-topological modules equipped with topological group actions
(G Ogp(G))∼
→ (G∗ Ogp(G∗)) induced by an isomorphism of topological
groupsG∼
→G∗ [sooneverifiesimmediatelythattheseisomorphismsarecompatible
with α◃,×μ, α∗
◃,×μ in the evident sense]; here, we note that any such isomorphism
(G Ogp(G))∼
→ (G∗ Ogp(G∗)) induces isomorphisms (G O×(G))∼
→ (G∗
O×(G∗)), (G O×μ(G))∼
→(G∗ O×μ(G∗))inafashioncompatiblewithα◃,×μ,
α∗
◃,×μ. The definition of coric data and isomorphisms of collections of coric data is
the same as in (v) [i.e., where one takes “Γ×μ” to be the image Im(Γ) of Γ ⊆ Z×].
The radial algorithm is the algorithm given by the assignment
(Π MTM(Π),G Ogp(G),α◃,×μ) → (G O×μ(G))
—whoseassociatedradialfunctorisfullandessentially surjective,hencedetermines
a multiradial environment.
(ix) Note that if G is a topological group isomorphic to Gk, then, in addi-
tion to G O×(G), G O×μ(G), one may also construct the log-shell I(G) ⊆
O×μ(G) [i.e., p−1 times the image of the G-invariants of O×(G) in O×μ(G) —
cf. [AbsTopIII], Proposition 5.8, (ii)]. In particular, if one replaces the nota-
tion “G O×μ(G)” in the discussion of (v), (vi), and (viii) by the notation
“(G O×μ(G),I(G) ⊆ O×μ(G))” [i.e., “G O×μ(G) equipped with its associ-
ated log-shell”], then one verifies immediately that one obtains a “log-shell version”
of the multiradial environments constructed in (v), (vi), and (viii).
Remark 1.8.1. In the context of the various examples given in Example 1.8,
(iii), (iv), (v), (vi), (vii), (viii), and (ix), it is useful to note that
no automorphism of O×μ(G) induced by an element of Aut(G) [e.g., an
element of G, regarded as an inner automorphism of G] coincides with an
automorphism of O×μ(G) induced by an element of Γ that has nontrivial
image in Z×
p.
42 SHINICHI MOCHIZUKI
Indeed, this follows immediately by observing that the composite with the p-adic
logarithm of the cyclotomic character of G determines [in light of the definition
of O×(G), in terms of abelianizations of open subgroups of G — cf. [AbsTopIII],
Proposition 5.8, (i)] a natural surjection O×μ(G) Qp, which [cf., e.g., [AbsAnab],
Proposition1.2.1,(vi)]isAut(G)-equivariant,relativetothetrivialactionofAut(G)
on Qp, and Γ-equivariant, relative to the natural action of Γ ⊆ Z× [via the natural
surjection Z× Z×
p ] on Qp.
Example 1.9. theoretic Algorithms.
Radial and Coric Data III: Graphs of Functorial Group-
(i) Let E and F be categories that arise from “types of mathematical data”
[cf. the discussion of Example 1.7, (i)]; Ξ : E → F a functor that arises from a
“functorial algorithm” [cf. the discussion of Example 1.7, (i)]. Then one may define
a new category G — that also arises from a “type of mathematical data” — as
follows: the objects of G are pairs (E,Ξ(E)), where E ∈ Ob(E), and Ξ(E) ∈ Ob(F)
is the image of E via Ξ; the morphisms of G are the pairs of arrows (f : E →
E′
,Ξ(f) : Ξ(E) → Ξ(E′)). We shall refer to G [or the “type of mathematical data”
that gives rise to G] as the graph of Ξ. Note that this construction was applied, in
eﬀect, in the discussion of the various radial environments constructed in Example
1.8. Finally, we observe that we have natural functors E → G [given by E →
(E,Ξ(E))], G → E [given by (E,Ξ(E)) → E], G → F [given by (E,Ξ(E)) → Ξ(E)].
(ii) In the notation of (i), suppose that E is the category of topological groups
isomorphic to Πtp
X
and isomorphisms of topological groups, and that Ξ is some
k
“functorial group-theoretic algorithm” [whose input data consists of a topological
group isomorphic to Πtp
X
]. Let (R,C,Φ) be the radial environment of Example 1.8,
k
(i). Then composing the functor R → E given by the assignment (Π,G,α) → Π
with Ξ : E → F yields a functor R → F, whose graph we denote by R†. Thus, by
considering the natural functors ΨR : R → R† [cf. (i)], R† → R → C, and taking
C† def
= C, we obtain a diagram as in the display of Example 1.7, (iv). Since (R,C,Φ)
is a multiradial environment, it thus follows that ΨR is multiradially defined [cf.
Example 1.7, (iv)]. That is to say, by using the radial environment of Example 1.8,
(i), one concludes that
any “functorial group-theoretic algorithm” whose input data consists of a
topological group isomorphic to Πtp
X
gives rise — in a tautological fashion
k
[cf. the discussion of tautological multiradializations in Example 1.7, (ii)]
— to a multiradially defined functor.
This approach will be discussed further in Remark 1.9.1 below.
(iii) On the other hand, one may also construct a radial environment as follows.
We define a collection of radial data to be a topological group Π isomorphic to Πtp
X
,
k
andanisomorphism of collections of radial datatobeanisomorphismoftopological
groups. The definitions of coric data and isomorphisms of collections of coric data
are the same as in Example 1.8, (i). The radial functor Φ : R → C is defined via the
assignment Π → Π/Δ [cf. the notation of Example 1.8, (i)]. Thus, Φ fails to be full
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 43
[cf., e.g., [AbsTopIII], §I3; [AbsTopIII], Remark 1.9.1]. That is to say, (R,C,Φ) is a
uniradial environment. Now suppose that Ξ : E → F is as in (ii). Then since R may
be identified with E, the graph of Ξ : R= E → F yields a category R† equipped
with natural functors ΨR : R → R†, Φ† : R† → R → C† def
= C. In particular, we
obtainadiagramasinthedisplayofExample1.7, (iv). Since(R,C,Φ)isauniradial
environment, it thus follows that ΨR is uniradially defined [cf. Example 1.7, (iv)].
That is to say, by using the radial environment just defined, one concludes that
any “functorial group-theoretic algorithm” whose input data consists of a
topological group isomorphic to Πtp
X
also gives rise — in a tautological
k
fashion — to a uniradially defined functor.
This approach will be discussed further in Remark 1.9.1 below.
(iv) Let Π be a topological group isomorphic to Πtp
X
; Δ ⊆ Π the subgroup
k
of Example 1.8, (i). Recall the isomorphism “μZ(Gk)∼
→ μZ(ΠX)” of [AbsTopIII],
Corollary 1.10, (c), which is constructed by means of a “functorial group-theoretic
algorithm”. The inverse of this isomorphism yields a cyclotomic rigidity isomor-
phism
(l·ΔΘ)(Π)∼
→ μZ(Π/Δ)
[cf. the discussion of Proposition 1.3, (ii)] — where we write “(l· ΔΘ)(Π)” for
the [group-theoretic!] subquotient of Π discussed in [EtTh], Corollary 2.18, (i).
Thus, in summary, one has a “functorial group-theoretic algorithm” whose input
data consists of the topological group Π, and whose output data may be thought of
as consisting of Π, the two topological Π-modules “(l·ΔΘ)(Π)”, “μZ(Π/Δ)”, and
the above isomorphism of Π-modules (l·ΔΘ)(Π)∼
→ μZ(Π/Δ). Thus, if one takes
this “functorial group-theoretic algorithm” to be the algorithm that gives rise to
the functor Ξ in the discussion of (ii) and (iii), then one concludes that the above
cyclotomic rigidity isomorphism (l· ΔΘ)(Π)∼
→ μZ(Π/Δ) may be thought of as
giving rise to either
(a) a multiradially defined functor, via the approach of (ii), or
(b) a uniradially defined functor, via the approach of (iii).
On the other hand, there is also another way to obtain a multiradially defined
functor from this cyclotomic rigidity isomorphism, as follows. Let (R,C,Φ) be the
multiradial environment of Example 1.8, (i). Now define a collection of daggered
radial data
(Π,G,α,(l·ΔΘ)(Π)∼
→ μZ(G))
to consist of radial data (Π,G,α) as in Example 1.8, (i), together with the poly-
isomorphism (l· ΔΘ)(Π)∼
→ μZ(G) obtained by composing the above cyclotomic
rigidityisomorphism“(l·ΔΘ)(Π)∼
→μZ(Π/Δ)”withthepoly-isomorphismμZ(Π/Δ)
∼
→ μZ(G) induced by the poly-isomorphism α : Π/Δ∼
→ G. Thus, the poly-
isomorphism (l· ΔΘ)(Π)∼
→ μZ(G) consists not of a single isomorphism of topo-
logical modules, but rather of an Aut(G)-orbit — or, more precisely, a Γ-orbit,
where Γ ⊆ Z× is the image of Aut(G) via the cyclotomic character on Aut(G) [cf.
[AbsAnab], Proposition 1.2.1, (vi)] — of isomorphisms of topological modules. An
44 SHINICHI MOCHIZUKI
isomorphism of collections of daggered radial data is defined to be an isomorphism
between the underlying collections of radial data [which is necessarily compatible
withthepoly-isomorphismoftopologicalmodulesthatconstitutesthefinalmember
ofthecollectionsofdaggeredradialdatainquestion]. Thus, ifwetakeC† def
= C, then
the “functorial group-theoretic algorithm” that gives rise to the cyclotomic rigid-
ity isomorphism “(l· ΔΘ)(Π)∼
→ μZ(Π/Δ)” yields a functor ΨR : R → R† [that
arises from a “functorial algorithm”], together with a diagram as in the display of
Example 1.7, (iv). That is to say,
(c) this multiradially defined functor ΨR : R → R† yields an alternative [i.e.,
relative to (a)] multiradial approach to representing the “functorial group-
theoretic algorithm” that gives rise to the cyclotomic rigidity isomorphism
“(l·ΔΘ)(Π)∼
→ μZ(Π/Δ)”.
This is the approach taken in Corollary 1.11, (b), below.
Remark 1.9.1. In general, the portion of the “functorial group-theoretic algo-
rithm” that appears in the discussion of Example 1.9, (ii), (iii), and (iv), which
involves the quotient Π/Δ of Π will depend not only on the structure of the ab-
stract topological group underlying Π/Δ, but also on the structure of Π/Δ as a
quotient of Π — i.e., from the point of view of the discussion of Example 1.8, (i), on
the “arithmetic holomorphic structure” on the topological group Π/Δ determined
by this quotient structure. In fact, the original motivation for the introduction of
the “multiradial terminology” of Example 1.7 was precisely to study the extent to
which such “functorial group-theoretic algorithms” could be formulated in such a
way as to compute
which portions of the output data of such algorithms do indeed depend
in an essential way on the “arithmetic holomorphic structure” and
which portions are “mono-analytic” [cf. [AbsTopIII], §I3], i.e., depend
only on the structure of the topological group Π/Δ [which one thinks of as
a sort of “underlying arithmetic real analytic structure” of the “arithmetic
holomorphic structures” involved].
From this point of view, the tautological approach of Example 1.9, (ii) [i.e., Example
1.9, (iv), (a)], may be thought of as expressing the idea that if one thinks of each
of the quotients “Π/Δ” in the “spokes” of Fig. 1.2 as being equipped with a fixed
“arithmetic holomorphic structure”andhenceonlyrelatedtothecoric“G”via some
indeterminate isomorphism of topological groups, then one obtains a multiradially
defined functor, i.e., a functor that is tautologically compatible with mono-analytic
deformations of the various “arithmetic holomorphic structures” that one might
impose on the coric “G”. Put another way, this multiradially defined algorithm is
an algorithm that is tautologically compatible with simultaneous execution on
multiple spokes of Fig. 1.2. By contrast, the tautological approach of Example
1.9, (iii) [i.e., Example 1.9, (iv), (b)], may be thought of as expressing the idea that
if one tries to identify the various quotients “Π/Δ” in the “spokes” of Fig. 1.2 via
arbitrary mono-analytic isomorphisms, then one only obtains a uniradially defined
functor, i.e., a functor that fails to be compatible with mono-analytic identifications
[i.e., gluing isomorphisms] of the various “arithmetic holomorphic structures” on
the coric “G”. Put another way, this uniradially defined algorithm is an algorithm
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 45
that can only be consistently executed on one spoke at a time. Finally, the ap-
proachofExample1.9, (iv), (c), expressestheideathat, inthecaseoftheparticular
cyclotomic rigidity isomorphism under consideration, if one weakens the rigidity of
this isomorphism by working with this isomorphism up to a certain indeterminacy,
then one may construct a multiradially defined functor, i.e., a functor that is indeed
compatible with mono-analytic identifications [i.e., gluing isomorphisms] of the var-
ious “arithmetic holomorphic structures” on the coric “G”, albeit up to a certain
specified indeterminacy. Thus, the multiradiality obtained in Example 1.9, (iv),
(c), depends, in an essential way, on the content of the “functorial group-theoretic
algorithm” involved. This approach taken in Example 1.9, (iv), (c), is representa-
tive of the approach taken in Corollaries 1.10, 1.11, and 1.12 below, which may be
thought of as “computations” of the “certain indeterminacy” that one must
allow in order to construct a multiradially defined functor as in Example 1.9, (iv),
(c).
Remark 1.9.2.
(i) One way to summarize the discussion of Remark 1.9.1 is as follows. If
uniradially defined functors correspond to constructions that depend, in a strict
sense, on the “arithmetic holomorphic structure”, while corically defined functors
correspond to constructions that only depend on the underlying mono-analytic
structure [i.e., “arithmetic real analytic structure”], then multiradially defined
functors correspond to constructions that depend on the “arithmetic holomorphic
structure”, but only in a fashion that is
compatible with a given description of how this arithmetic holomorphic
structure is related to — e.g., “embedded in” — the underlying mono-
analytic structure.
For instance, in the various multiradial environments of Example 1.8, this descrip-
tion of the relation to the underlying mono-analytic structure is given, at a concrete
level, by the various poly-morphisms [or diagrams of poly-morphisms] “α(−)” that
appear in the radial data of these multiradial environments. This point of view is
summarized in Fig. 1.3 below.
(ii)FromthepointofviewoftheanalogywithconnectionsdiscussedinRemark
1.7.1, one may think of a multiradial environment as a structure that allows one to
execute parallel transport operations between distinct arithmetic holomorphic
stuctures, i.e., to describe what one arithmetic holomorphic structure looks like
from the point of view of a distinct arithmetic holomorphic structure that is only
related to the original arithmetic holomorphic structure via the mono-analytic core.
(iii) From the point of view of the analogy with connections discussed in Re-
mark 1.7.1, it is also interesting to observe that one may think of the diﬀerent ap-
proaches to multiradiality discussed in Example 1.9, (iv), (a), (c), as being roughly
analogous to the phenomenon of distinct connection structures on a single
fibration. Moreover, of these diﬀerent approaches, the tautological, “general non-
sense” approach of Example 1.9, (iv), (a), is, in some sense, [not surprisingly!] the
“least interesting” [although it will at times be of use in the theory of the present
series of papers!]. This sort of “general nonsense” approach is reminiscent of the
46 SHINICHI MOCHIZUKI
tautological approach to constructing connections that occurs in the p-adic theory
of the crystalline site, i.e., by simply forming the tensor product with
the ring of functions of the PD-envelope along the diagonal of the fiber
product of two copies of the space under consideration.
From the point of view of the issue of “describing what one arithmetic holomorphic
structure looks like from the point of view of another” [cf. (ii)], the “tautological”
approach is not very interesting precisely because it involves working, in eﬀect, with
the “tautological” collection of“labels of all possible arithmetic holo-
morphic structures” — i.e., corresponding to the various choices of one
particular arrow among the arrows that constitute the poly-morphism
denoted “α” in Example 1.8, (i) — without describing in further, more
explicit terms what these various “alien” arithmetic holomorphic struc-
tures look like relative to structures determined by a given arithmetic
holomorphic structure.
By contrast, the “non-tautological” approach to multiradiality of Example 1.9, (iv),
(c), by means of the explicit computation of indeterminacies is much more
interesting in that it yields a more detailed, explicit description of a structure [e.g.,
a cyclotomic rigidity isomorphism] associated to an “alien” arithmetic holomorphic
structure in terms of the structure associated to a given arithmetic holomorphic
structure.
abstract general nonsense inter-universal Teichm¨ uller theory classical complex
Teichm¨ uller theory
uniradially defined functors arithmetic holomorphic structures holomorphic
structures
multiradially defined functors arithmetic holomorphic structures described in terms of underlying mono-analytic structures holomorphic
structures described in
terms of underlying
real analytic structures
corically defined functors underlying mono-analytic structures underlying real analytic
structures
Fig. 1.3: Uniradiality, Multiradiality, and Coricity
We now proceed to discuss our main results concerning multiradiality.
Corollary 1.10. (Multiradial Mono-theta Cyclotomic Rigidity Isomor-
phisms) Write (R,C,Φ : R → C) — i.e., in the notation of Example 1.8, (v),
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 47
(vi),
(Π Πμ(MΘ
∗ (Π))⊗Q/Z,G O×μ(G),αμ,×μ) → (G O×μ(G))
— for the multiradial environment constituted by the exterior-cyclotomic
version [cf. Example 1.8, (vi)] of the multiradial environment discussed in Example
1.8, (v). Consider the cyclotomic rigidity isomorphism
(l·ΔΘ)(Π)∼
→ Πμ(MΘ
∗ (Π)) (∗mono-Θ
Π )
[where we identify (l·ΔΘ)(MΘ
∗ (Π)) with (l·ΔΘ)(Π) — cf. Proposition 1.4] obtained
by composing the functorial algorithm Π → MΘ
∗ (Π) of Proposition 1.2, (i) [cf. also
Proposition 1.5, (i)], with the functorial algorithm for constructing a cyclotomic
rigidity isomorphism of Proposition 1.5, (iii). Then the data consisting of the topo-
logical group Π, the topological Π-modules constituted by the domain and codomain
of (∗mono-Θ
Π ), and the isomorphism (∗mono-Θ
Π ) determines a functor R → F [i.e.,
where F denotes the category defined in the evident way so as to accommodate the
data just listed] which arises from a functorial algorithm in the topological group
Π; denote the corresponding graph [cf. Example 1.9, (i)] by R†. In particular, the
resulting natural functor ΨR : R → R† [cf. Example 1.9, (i)] is multiradially
defined.
Proof. nitions involved. ⃝
The various assertions of Corollary 1.10 follow immediately from the defi-
Remark 1.10.1. We recall in passing that the domain and codomain of the iso-
morphism (∗mono-Θ
Π ) of Corollary 1.10, as well as the isomorphism (∗mono-Θ
Π ) itself,
are constructed from various subquotients of [the projective system of topological
groups] ΔMΘ
∗ (Π) which are completely determined by the structure of ΔMΘ
∗ (Π) as
a projective system of topological groups, the subgroups of ΔMΘ
∗ (Π) determined by
the images of the “theta section” portions of the system of mono-theta environ-
ments MΘ
∗ (Π), and the images [arising from the natural outer actions involved
— cf. Definition 1.1, (i)] of (l· Z)(MΘ
∗ (Π)) and G(MΘ
∗ (Π)) in Out(ΔMΘ
∗ (Π)). In-
deed, the algorithms described in the proofs of [EtTh], Corollary 2.18, (i), (iii);
[EtTh], Corollary 2.19, (i), for constructing the various subquotients of ΔMΘ
∗ (Π)
corresponding to the domain and codomain of (∗mono-Θ
Π ), as well as to the graph
of the isomorphism (∗mono-Θ
Π ) itself, depend only on the structure of the projective
system of topological groups ΔMΘ
∗ (Π) [cf., e.g., [EtTh], Proposition 2.11, (i)], the
subgroups of ΔMΘ
∗ (Π) determined by the images of the “theta section” portions of
the system of mono-theta environments MΘ
∗ (Π) [cf. [EtTh], Definition 2.13, (ii),
(c)], and the construction of the group ΔC(Π) [which was reviewed in Proposition
1.6, (i)] containing (ΔMΘ
∗ (Π) ) ΔY (MΘ
∗ (Π)) ⊆ ΔX(MΘ
∗ (Π))∼
= Δ, which is used to
construct the various subquotients that appear in the crucial [EtTh], Proposition
2.12; [EtTh], Proposition 2.14, (i).
Remark 1.10.2. In words, the content of Corollary 1.10 may be understood as
follows:
48 SHINICHI MOCHIZUKI
Since O×μ(G) is constructed by forming the quotient of O×(G) by the
roots of unity [i.e., Oμ(G)] — recall the triviality of the homomorphism
Πμ(MΘ
∗ (Π))⊗Q/Z → O×μ(G) [cf. Example 1.8, (v), (vi)]! — any rigidifi-
cation of the cyclotome Πμ(MΘ
∗ (Π)) that depends only on the structure
of the mono-theta-environment MΘ
∗ (Π) will be tautologically com-
patible with the coricity of O×μ(G), i.e., with the “sharing of O×μ(G)”
by distinct arithmetic holomorphic structures[cf. thediscussionofRemark
1.9.1; Fig. 1.4 below].
This contrasts sharply with the situation to be considered in Corollary 1.11 below
— cf. Remarks 1.11.3, 1.11.4, below. A similar statement may be made concerning
the subquotient (l·ΔΘ)(Π) of Δ ⊆ Π, which maps trivially to Π/Δ∼
→ G.
iΠ
...
⏐ ⏐...
i′
Π −→ G O×μ(G) Γ×μ ←− i′′
Π
... ⏐ ⏐...
i′′′
Π
Fig. 1.4: A single coric pair G O×μ(G), regarded up to the action of Γ×μ
Remark 1.10.3. In the context of Corollary 1.10, it is useful to recall the
following [cf. the discussion of [EtTh], Remark 1.10.4, (ii)]. Although at first
glance, it might appear as though it might be possible to develop a similar theory
to the theory developed in the present series of papers based on a more general
sort of meromorphic function than the theta function, it is by no means clear
that such a more general meromorphic function satisfies the crucial cyclotomic
rigidity, discrete rigidity, and constant multiple rigidity properties studied
in [EtTh]. Of these properties, the cyclotomic rigidity property, which forms the
basis of Corollary 1.10, depends most explicitly [cf. [EtTh], Remark 2.19.2] on
the structure of the theta quotient 1 → ΔΘ → ΔΘ
X → Δell
X → 1 reviewed in
[IUTchI], Remark 3.1.2, (iii) [cf. also the discussion of Remark 1.1.1 of the present
paper], i.e., which corresponds to the “theta group” in more classical treatments
of the theta function. Since the theta function is, roughly speaking, essentially
characterized among meromorphic functions by the property that it satisfies the
“theta symmetries” arising from the theta group, it is thus diﬃcult to see how
to generalize the theory of the present series of papers so as to treat more general
meromorphic functions than the theta function [cf. Remark 1.1.1, (v); [IUTchIII],
Remark 2.3.3, for a more detailed discussion of related issues]. Also, in this context,
it is useful to recall that unlike the theta function itself, which is strictly local
in nature [i.e., in the sense that it is only defined, a priori, at v ∈ Vbad], the
theta quotient ΔΘ
X, hence, in particular, the subquotient ΔΘ, is defined globally [cf.
the discussion of [IUTchI], Remark 3.1.2] over the various number fields involved,
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 49
hence may be applied to the execution of various global anabelian reconstruction
algorithms via the“Θ-approach” [cf. [IUTchI], Remark 3.1.2].
Corollary 1.11. (Multiradial MLF-Galois Pair Cyclotomic Rigidity
Isomorphisms with Indeterminacies) Write (R,C,Φ : R → C) — i.e., in the
notation of Example 1.8, (viii),
(Π MTM(Π),G Ogp(G),α◃,×μ) → (G O×μ(G))
— for the multiradial environment discussed in Example 1.8, (viii). Consider
(a) the Γ-orbit [where we recall that Γ ⊆ Z× is a closed subgroup]
μZ(G)∼
→ μZ(O×(G)) def = Hom(Q/Z,O×(G)) (∗bs-Gal
G,◃ )
of the cyclotomic rigidity isomorphism obtained by applying to the
MLF-Galois pair determined by G O◃(G) the algorithm applied to
construct [the inverse of] the isomorphism “μZ(MTM)∼
→ μZ(G)” in [Ab-
sTopIII], Remark 3.2.1 [cf. the discussion of Proposition 1.3, (ii)]; and
(b) the Aut(G)-orbit [where we recall from [AbsAnab], Proposition 1.2.1,
(vi), that Aut(G) admits a natural cyclotomic character] of isomorphisms
μZ(G)∼
→ (l·ΔΘ)(Π) (∗bs-Gal
G,Π )
obtained by composing the poly-isomorphism induced by applying “μZ(−)”
to the [inverse of the] full poly-isomorphism of topological groups α :
Π/Δ∼
→ G [cf. Example 1.8, (i)] with the natural isomorphism“μZ(Gk)
∼
→ μZ(ΠX)” of [AbsTopIII], Corollary 1.10, (c) [cf. the discussion of
Proposition 1.3, (ii)].
Then the data consisting of the triple (Π,G,α) [cf. Example 1.8, (i)], the topological
G-modules constituted by the domain and codomain of (∗bs-Gal
G,◃ ), the topological Π-
module constituted by the codomain of (∗bs-Gal
G,Π ), and the poly-isomorphisms (∗bs-Gal
G,◃ )
and (∗bs-Gal
G,Π ) determines a functor R → F which arises from a functorial algorithm
in the triple (Π,G,α); denote the corresponding graph [cf. Example 1.9, (i)] by
R†. In particular, the resulting natural functor ΨR : R → R† [cf. Example 1.9,
(i)] is multiradially defined.
Proof. nitions involved. ⃝
The various assertions of Corollary 1.11 follow immediately from the defi-
Remark 1.11.1.
(i) In the context of Corollary 1.11, it is useful to recall that:
(a) the group of automorphisms of the underlying ind-topological monoid
equipped with a topological group action — i.e., in the terminology of
[AbsTopIII], Definition 3.1, (ii), MLF-Galois TM-pair — of
G O◃(G)
50 SHINICHI MOCHIZUKI
maps bijectively [i.e., by forgetting “O◃(G)”] onto the group of automor-
phisms of the topological group G [cf. [AbsTopIII], Proposition 3.2, (iv)];
(b) the group of automorphisms of the underlying ind-topological module
equipped with a topological group action — i.e., in the terminology of
[AbsTopIII], Definition 3.1, (ii), MLF-Galois TCG-pair — of
G O×(G)
maps surjectively [i.e., by forgetting “O×(G)”] onto the group of auto-
morphisms of the topological group G, with kernel given by the [G-linear]
automorphisms of [the underlying ind-topological module of] O×(G) de-
termined by the natural action of Z× [cf. [AbsTopIII], Proposition 3.3,
(ii)].
Also, we observe that by the same proof involving the Kummer map as that given
for (b) in [AbsTopIII], Proposition 3.3, (ii), it follows that
(c) the group of automorphisms of the underlying ind-topological module
equipped with a topological group action of
G Ogp(G)
maps surjectively [i.e., by forgetting “Ogp(G)”] onto the group of auto-
morphisms of the topological group G, with kernel given by the [G-linear]
automorphisms of [the underlying ind-topological module of] Ogp(G) de-
termined by the natural action of Z× [or, equivalently, maps bijectively
onto the group of automorphisms of the underlying ind-topological mod-
ule equipped with a topological group action of G O×(G) — cf. (b)].
On the other hand, one verifies immediately that
(d) the underlying ind-topological module of O×μ(G) is divisible, hence
admits a natural action by Qp.
In particular, if, in (b), one replaces “O×” by “O×μ”, then the resulting description
of the kernel is false.
(ii) In the present series of papers, we shall primarily be interested in Corollary
1.11 in the case where
Γ = Z×
.
Thatistosay, allowingforaΓ (= Z×)-multiple indeterminacycorrespondsprecisely
to working, in the case of G O×(G), with the underlying ind-topological module
equipped with topological group action [cf. (i), (b)].
Remark 1.11.2.
(i) Observe that, in the context of the discussion of Remark 1.11.1, (i), (b),
the natural action of Z× on [the underlying ind-topological module equipped with
a topological group action of] G O×(G) is compatible with pull-back via the
composite of the natural surjection Π Π/Δ with any isomorphism Π/Δ∼
→ G [cf.
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 51
the notation of Example 1.8]. That is to say, one has a natural action of Z× on [the
underlying ind-topological module equipped with a topological group action of] the
resulting pair Π O×(G). Observe, moreover, that this action of Z× fails to be
compatible with the ring structure on O×(G)⊗Q [i.e., the ring structure determined
by applying the p-adic logarithm]. That is to say, even though this ring structure
on “O×” may [unlike the case with G!] be reconstructed from the topological group
Π [cf. [AbsTopIII], Theorem 1.9], the natural action of Z× on Π O×(G) fails to
preserve the ring structure reconstructed from Π.
(ii) The observations of (i) are of interest in the context of understanding our
adoption of“G” as opposed to “Π” in the construction of the “Θ-link” between
distinct Θ-Hodge theatersgivenin[IUTchI],Corollary3.7. Thatistosay, evenifone
triesto“force a preservation of arithmetic holomorphic structures”betweendistinct
Θ-Hodge theaters by working with “Π O×(G)” instead of “G O×(G)”, this
does not result in the establishment of a consistent common arithmetic holomorphic
structure for distinct Θ-Hodge theaters, since the establishment of such a consistent
common arithmetic holomorphic structure is already obstructed by the fact that
distinct Θ-Hodge theaters only share a common “O×” [cf. [IUTchI], Corollary 3.7,
(iii)] — on which Z× acts [cf. (i)] — i.e., as opposed to a common “O◃”. Here, we
recall that the establishment of a common “O◃” is obstructed, in a quite essential
manner, by the “valuative portion †Θ
v
→ ‡q
” of the Θ-link [cf. [IUTchI], Remark
v
3.8.1, (i)].
Remark 1.11.3.
(i) In some sense, the starting point of any discussion of radial environments is
the description of the radial functor, i.e., the specification of “which portion of the
radial data one takes for one’s coric data”. From the point of view of the theory
of [IUTchI], §3 [cf., especially, the portion at v ∈ Vbad of [IUTchI], Corollaries 3.7,
3.9], the coric data should, in particular, include the quotient Π Π/Δ∼
= G of the
topological group Π isomorphic to Πtp
X
that appears in a Θ-Hodge theater. On the
k
other hand, in [IUTchIII], we shall ultimately be interested in applying the theory
of [AbsTopIII], §3, §5, in which various objects [such as “Π MTM(Π)”, “G
O◃(G)”, “G O×(G)”, etc.] are constructed group-theoretically from Π or G. One
important aspect of the theory of [AbsTopIII], §3, §5, is that after these objects
are constructed group-theoretically from Π or G, one then proceeds to forget the
“anabelian structure” of these objects, i.e., one forgets the data consisting of
the way in which these objects [such as MLF-Galois TM-pairs, MLF-Galois TCG-
pairs, etc.] are constructed from Π or G. From the point of view of the issue of
“specificationofcoricdata”, ifonetakes, forinstance, “G”tobeapartofone’scoric
data, thenanyobjectsconstructedgroup-theoreticallyfromGmayalsoberegarded
naturally as constituting a portion of the coric data — so long as one regards
these objects as being equipped with the corresponding “anabelian structures” [i.e.,
the data that specifies the way in which they were constructed group-theoretically
from G]. On the other hand, once one forgets these anabelian structures, it is no
longer the case that such an object may also be regarded naturally as constituting
a portion of the coric data. That is to say, once one forgets the anabelian structure
of such an object, it is necessary to specify explicitly that such an object is to
52 SHINICHI MOCHIZUKI
be regarded as a portion of the coric data, i.e., as a portion of the radial data that
is to be subject to the “gluing”, or “identification”, discussed in Example 1.7,
(v).
(ii) In light of the “coricity of O×” given in [IUTchI], Corollary 3.7, (iii), in
addition to “G”, it is possible to take the underlying MLF-Galois TCG-pair of
“G O×(G)” to be part of one’s coric data. By applying Remark 1.11.1, (i), (b),
it follows that this amounts to working with “G O×(G)” up to an (Aut(G),Γ (=
Z×))-indeterminacy—wherewerecallfromRemark1.8.1thatthep-adicportionof
the Γ-indeterminacy cannot be subsumed into the Aut(G)-indeterminacy [i.e., which
arises from the fact that G is only known up to isomorphism as a topological group].
This situation is precisely the situation formulated in Example 1.8, (iii). On the
other hand, as we saw already in Corollary 1.10 [cf. Remark 1.10.2], and as we shall
see again in Corollary 1.12 below, in order to construct certain multiradially defined
functors that will be of substantial importance in the development of the theory
of the present series of papers, it is necessary to form the quotient of “O×(−)” by
its torsion subgroup “Oμ(−)”, i.e., to work with “O×μ(−)”, rather than “O×(−)”.
Here, we note [cf. Example 1.8, (ix); Remark 1.11.1, (i), (d)] that one does not
wish here to work solely with the underlying ind-topological module equipped with
topological group action determined by “G O×μ(G)”. On the other hand, by
applying [IUTchI], Corollary 3.7, (iii), together with Remark 1.11.1, (i), (b), one
concludes that it is possible
to glue together, in a consistent fashion, the various “G O×μ(G)” [cf.
Fig. 1.4] arising from distinct Θ-Hodge theaters up to an (Aut(G),Γ (=
Z×))-indeterminacy
[where again we recall from Remark 1.8.1 that the p-adic portion of the Γ-indeter-
minacy cannot be subsumed into the Aut(G)-indeterminacy]. This sort of situation
is formulated in the radial environments of Example 1.8, (v), (vi), (viii), (ix) [i.e.,
where one takes “Γ×μ” to be the image Im(Γ) of Γ]. One important point in this
context is that even if one takes “G O×μ(G)” [i.e., as opposed to “G O◃(G)”,
“G Ogp(G)”, or“G O×(G)”]asone’scoricdata, theconditionofcompatibility
with respect to the natural maps
Ogp(G) ← O×(G) O×μ(G)
[cf. Example 1.8, (viii)] implies that
the (Aut(G),Γ (= Z×))-indeterminacy on “G O×μ(G)” induces a
(Aut(G),Γ (= Z×))-indeterminacy on “G O×(G)” and “G Ogp(G)”
— where one may think of the “Γ-indeterminacy on Ogp(G)” as representing the
“Γ-indeterminacy in the specification of the submonoid O◃(G) ⊆ Ogp(G)”. It is
precisely these indeterminacies that induce the indeterminacies — i.e., “orbits”—
that appear in Corollary 1.11, (a), (b), in sharp contrast to the “strict cyclotomic
rigidity” [i.e., without any indeterminacies] of Corollary 1.10 [cf. Remark 1.10.2].
(iii) Note that the algorithms applied to construct cyclotomic rigidity iso-
morphisms in Corollaries 1.10 and 1.11, (a), are obtained by composing with a
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 53
group-theoretic construction algorithm an algorithm whose input data is “post-
anabelian” — i.e., consists of a type of mathematical object that arises upon
forgetting the anabelian structure determined by the group-theoretic construction
algorithm. More concretely, this post-anabelian input data consists of a system of
mono-theta environments in the case of Corollary 1.10 and of an MLF-Galois TM-
pair in the case of Corollary 1.11, (a). As discussed in (ii), the indeterminacies that
act on this post-anabelian input data induce the indeterminacies — i.e., “orbits”
— that appear in Corollary 1.11, (a), (b). Put another way,
(a) the indeterminacies — i.e., “orbits” — that appear in Corollary 1.11, (a),
(b), are a consequence of the highly nontrivial relationship [cf. the dis-
cussion of (ii)] between the input data “O◃(−)” of the cyclotomic rigidity
algorithm involved and the coric data “O×μ(−)”
.
By contrast,
(b) the“strictcyclotomicrigidity”assertedinCorollary1.10isaconsequence
[cf. Remark 1.10.2] of the triviality of the homomorphism that relates
the cyclotomic portion of “O◃(−)” — which is the only portion of
“O◃(−)” that appears in a mono-theta environment — to the coric
data “O×μ(−)”
.
Here, it is important to note that although frequently in discussions of various “re-
construction algorithms” [such as group-theoretic reconstruction algorithms], em-
phasis is placed on the existence of “some” reconstruction algorithm, the present
discussion of the multiradiality of cyclotomic rigidity isomorphisms in the con-
text of Corollaries 1.10, 1.11 yields an important example of the phenomenon that
sometimes not only the existence of “some” reconstruction algorithm, but also the
content of the reconstruction algorithm [cf. the discussion of [IUTchIV], Example
3.5] is of crucial importance in the development of the theory.
(iv) Here, we note in passing that one may eliminate the (Aut(G),Γ)-indeter-
minacy of Corollary 1.11, (a), (b), by working, in the fashion of Example 1.9, (iv),
(b), with uniradially defined functors [that is to say, in the case of Corollary
1.11, (a), (b), replacing “G O◃(G)” by “Π MTM(Π)” and “G” by “Π/Δ” and
working with the uniradial environment corresponding to the assignment
(Π MTM(Π)) → (Π/Δ M×μ
TM (Π))
— i.e., for which the definition of the coric data coincides with the definition of the
coric data of the multiradial environment in the statement of Corollary 1.11].
(v) The reason [cf. the discussion of (iii)] that we wish to consider cyclotomic
rigidity algorithms whose input data is post-anabelian is that we wish to be able
to apply the same algorithms to input data that does not necessarily arise from a
group-theoretic construction algorithm — e.g., to input data that arises from the
[divisor and rational function] monoid portion of a Frobenioid, as in Proposition
1.3. In the context of Proposition 1.3, the exterior cyclotome of the mono-theta en-
vironment that appears in Corollary 1.10 and the cyclotome arising from “O◃(−)”
thatappearsinCorollary1.11,(a),bothcorrespondtothesame cyclotome“μN(S)”
[which arises from the monoid portion of the Frobenioid involved]. On the other
hand, at the level of construction algorithms, in order to relate the exterior cyclo-
tome “Πμ(MΘ
∗ (Π))” of Corollary 1.10 to the cyclotome “μZ(O×(G))” of Corollary
54 SHINICHI MOCHIZUKI
1.11, (a), it is necessary [cf. Proposition 1.3, (iii)] to pass through the cyclotome
“(l·ΔΘ)(Π)” by applying the cyclotomic rigidity isomorphisms of Corollaries 1.10,
1.11 — which, in the case of Corollary 1.11, results in various indeterminacies. Put
another way, the Frobenioid-theoretic identification [i.e., via “μN(S)”] of Proposi-
tion 1.3 between the cyclotomes “Πμ(MΘ
∗ (Π))”, “μZ(O×(G))” of Corollaries 1.10;
1.11, (a), may be thought of either as being only uniradially defined [cf. (iv)],
or as multiradially defined, but only up to certain indeterminacies.
Remark 1.11.4.
(i) One way to understand the significance of the cyclotomic rigidity isomor-
phismobtainedinCorollary1.10—i.e., ofthetriviality ofthehomomorphismthat
relates the cyclotomic portion of “O◃(−)” to the coric data “O×μ(−)” [cf. Remark
1.11.3, (iii), (b)]—relativetothecyclotomicrigidityisomorphismofCorollary1.11,
which involves substantial indeterminacies arising from the highly nontrivial re-
lationship between the input data “O◃(−)” of the cyclotomic rigidity algorithm
involved and the coric data “O×μ(−)” [cf. Remark 1.11.3, (iii), (a)], is as a sort of
splitting, or decoupling, that serves to separate the “purely radial
data” that appears in the cyclotomic rigidity isomorphism of Corollary
1.10 from the “purely coric data” constituted by “O×μ(−)”.
This point of view is discussed further in Remark 1.12.2, (vi), below.
(ii) From the point of view of the discussion of Remark 1.9.2, (iii), the “purely
radial data” that appears in the cyclotomic rigidity isomorphism of Corollary 1.10
depends on the tautological collection of“labels of all possible arithmetic holo-
morphic structures”. That is to say, the algorithms of Corollary 1.10 do not give
rise to a “detailed, explicit description” of these labels in terms of the “purely coric
data O×μ(−)”. On the other hand, one may also consider a modified version of
Corollary 1.10 in which
(∗) one replaces “O×μ(−)” by “O×(−)” [i.e., so that the crucial triviality
discussed in Remark 1.11.3, (iii), (b), no longer holds!] and applies the
tautological approach discussed in Example 1.9, (iv), (a), to construct-
ing the cyclotomic rigidity isomorphism [without indeterminacies!] under
consideration.
If one works with this modified version (∗), then the codomain of the cyclotomic
rigidity isomorphism under consideration may be thought of as the submodule
“Oμ(−)” of the “purely coric data O×(−)”, equipped with a “certain rigidity” that
depends on the choice of an element of the collection of “labels of all possible
arithmetic holomorphic structures”. That is to say, whereas Corollary 1.10 has
the drawback of being “not entirely free of label-dependence”, the significance of
Corollary 1.10 [as stated!] relative to the tautological modified version (∗) lies in
the fact that the label-dependence inherent in Corollary 1.10 is confined to the
“purely radial component” of the splitting, or decoupling, discussed in (i) — i.e.,
unlike the case with (∗), the algorithms of Corollary 1.10 yield a “purely coric
component” that is free of such “unwanted” label-dependent data. Thus,
in summary, unlike the case with (∗), the algorithms of Corollary 1.10 yield out-
put data equipped with a splitting, or decoupling, into label-dependent [i.e.,
“purely radial”] and label-independent [i.e. “purely coric”] components.
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 55
Remark 1.11.5. Suppose that we are in the situation of Corollary 1.11.
(i) Recall the natural surjection
H1(G,μZ(G)) Z
— which is constructed via a functorial group-theoretic algorithm in [AbsTopIII],
Corollary 1.10, (b). That is to say, when G= Gk, this surjection is the surjection
determined by the valuation of k on the image of the natural Kummer map
k× → H1(Gk,μZ(Gk))
— where we recall that the image of this Kummer map is equal to the inverse image
of Z ⊆ Z via the surjection under consideration. In particular, the existence of this
functorial group-theoretic algorithm implies that the data consisting of this natural
surjection — hence, in particular, its kernel, i.e., “O×
k ” — may be formulated as a
corically, hence, in particular, as a multiradially [cf. Example 1.7, (iv)], defined
functor. [We leave the routine details to the reader.]
(ii) On the other hand, if one applies the isomorphisms (∗bs-Gal
G,◃ ) [cf. also the
poly-isomorphism α◃ of Example 1.8, (ii)] and (∗bs-Gal
G,Π ), of Corollary 1.11, then the
natural surjection of (i) gives rise to natural surjections
H1(G,μZ(MTM(Π))) Z; H1(G,(l·ΔΘ)(Π)) Z
—whichyielddatathatmaybeformulatedeitherasauniradially defined functor
[cf. Remark 1.11.3, (iv)] or, when considered up to a Z×-indeterminacy, as a
multiradially defined functor [cf. Corollary 1.11]. In particular, the kernels of
these natural surjections yield data that may be formulated as a multiradially
defined functor. [We leave the routine details to the reader.]
Remark 1.11.6. The importance of cyclotomic rigidity in the theory of the
present series of papers is interesting in light of the analogy between the ideas of
the present series of papers and the p-adic Teichm¨ uller theory of [pTeich] [cf. the
discussion of [AbsTopIII], §I5]. Indeed, the proof of a fundamental absolute p-adic
anabelian result concerning the canonical curves that arise in the theory of [pTeich]
[cf. [CanLift], Theorem 3.6] depends, in an essential way, on a certain cyclotomic
rigidity result proven in an earlier paper [cf. [AbsAnab], Lemma 2.5, (ii)]. In this
context, we observe that one important theme that appears both in the present
series of papers and in the theory of [CanLift], §3, is the idea that cyclotomes
should be thought of as the “skeleta of arithmetic holomorphic structures”
— cf. the relation of S1 to C× in the complex archimedean theory.
We are now ready to discuss the main result of the present §1.
Corollary 1.12. (Multiradial Constant Multiple Rigidity) Write (R,C,Φ :
R → C) — i.e., in the notation of Example 1.8, (v), (vi),
(Π Πμ(MΘ
∗ (Π))⊗Q/Z,G O×μ(G),αμ,×μ) → (G O×μ(G))
56 SHINICHI MOCHIZUKI
— for the multiradial environment discussed in Example 1.8, (v), (vi), where
we take Γ×μ def = Ism. Consider the functorial algorithm that associates to
Π
the following commutative diagram (†×θ)(Π)
M×
TM(Π) M×
TM·
∞θ(Π) → lim
− →J H1(Π¨
Y (Π)|J,(l·ΔΘ)(Π))
⏐ ⏐ ⏐ ⏐
M×
TM(MΘ
∗ (Π)) M×
TM·
∞θ
env(MΘ
∗ (Π)) → lim
− →J H1(Π¨
Y (MΘ
∗ (Π))|J,Πμ(MΘ
∗ (Π)))
— where
(a) J ranges over the finite index open subgroups of Π; “|J” denotes the fiber
product “×ΠJ”;
(b) the right-hand vertical arrow is the isomorphism of modules induced
by the cyclotomic rigidity isomorphism obtained via the functorial
algorithm of Corollary 1.10;
(c) we recall that it follows from the definitions [cf. Example 1.8, (ii), (iii);
[AbsTopIII], Definition 3.1, (vi); [IUTchI], Remark 3.1.2] that one has a
natural inclusion M×
TM(Π) → lim
− →J H1(J,(l· ΔΘ)(Π)), hence a natural
inclusion of M×
TM(Π) into the inductive limit of the first line;
(d) we define M×
TM(MΘ
∗ (Π)) and the left-hand vertical arrow to be the sub-
module and bijection induced by the cyclotomic rigidity isomorphism of
(b);
(e) we define M×
TM·
∞θ(Π) def
= M×
TM(Π)·
∞θ(Π); here,∞θ(Π) is obtained via
the functorial algorithm of Proposition 1.4, applied to Π, and the “·” is
to be understood as being taken with respect to the module structure [i.e.,
which is usually denoted additively!] of the ambient cohomology module;
(f) we define M×
TM·
∞θ
env(MΘ
∗ (Π)) def
= M×
TM(MΘ
∗ (Π))·
∞θ
env(MΘ
∗ (Π)); here,
∞θ
env(MΘ
∗ (Π)) is obtained via the functorial algorithm of Proposition 1.5,
(iii), applied to MΘ
∗ (Π) [cf. Propositions 1.2, (i); 1.5, (i)]; the “·” is as
in (e);
(g) the horizontal arrows “→” are the natural inclusions.
Also, let us write M×μ
TM (−) def
= M×
TM(−)/Mμ
TM(−), where Mμ
TM(−) ⊆ M×
TM(−) de-
notes the submodule of torsion elements. Then:
(i) There is a functorial group-theoretic algorithm
Π → {(ι,D)}(Π)
that assigns to the topological group Π a collection of pairs (ι,D) — where Δ¨
Y (Π) def
=
Π¨
Y (Π) Δ, ι is a Δ¨
Y (Π)-outer automorphism of Π¨
Y (Π) [cf. Proposition 1.4], and
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 57
[by abuse of notation] D ⊆ Π¨
Y (Π) is a Δ¨
Y (Π)-conjugacy class of closed subgroups
— with the property that when Π = Πtp
X
, the resulting collection of pairs coincides
k
with the collection of “pointed inversion automorphisms” of Remark 1.4.1, (ii).
Here, each pair (ι,D) will be referred to as a pointed inversion automorphism.
If (ι,D) is a pointed inversion automorphism, and ι induces an “action up to
torsion” on some subset “(−)” of an abelian group [i.e., an action on the image
of this subset in the quotient of the abelian group by its torsion subgroup], then we
shall denote by a superscript “ι” on “(−)” the subset of ι-invariants with respect
to this “action up to torsion”, i.e., the subset of “(−)” that consists precisely of
those elements of “(−)” whose images in the quotient of the abelian group by its
torsion subgroup are fixed by the induced action of ι.
(ii) Let (ι,D) be a pointed inversion automorphism associated to Π [cf. (i)].
Then restriction to the subgroup D ⊆ Π¨
Y (Π) determines [the horizontal arrows
in] a commutative diagram
{M×
TM·
{M×
TM·
∞θ(Π)}ι −→ M×
TM(Π) ⊆ lim
− →J H1(J,(l·ΔΘ)(Π))
⏐ ⏐ ⏐ ⏐
∞θ
env(MΘ
∗ (Π))}ι −→ M×
TM(MΘ
∗ (Π)) ⊆ lim
− →J H1(J,Πμ(MΘ
∗ (Π)))
— where J ranges over the finite index open subgroups of Π [cf. (a)]; the vertical
arrows are the isomorphisms induced by the cyclotomic rigidity isomorphism of
Corollary 1.10 [cf. (b)]. Here, the inverse images of the submodules of torsion
elements — i.e., [up to various natural isomorphisms] the submodules “Mμ
TM(−)”
— via the upper and lower horizontal arrows are given, respectively, by∞θ(Π)ι and
∞θ
env(MΘ
∗ (Π))ι. In particular, we obtain a functorial algorithm [in the topological
group Π] for constructing splittings
M×μ
TM (Π) × {∞θ(Π)ι/Mμ
TM(Π)};
M×μ
TM (MΘ
∗ (Π)) × {∞θ
env(MΘ
∗ (Π))ι/Mμ
TM(MΘ
∗ (Π))} (†μθ)(Π)
— i.e., direct product decompositions inside the quotients of the inductive limits
on the right-hand side of the diagram (†×θ)(Π) by “Mμ
TM(−)” — of the respective
images of {M×
TM·
∞θ(Π)}ι
, {M×
TM·
∞θ
env(MΘ
∗ (Π))}ι in these quotients.
(iii) Consider the assignment that associates to the data
(Π Πμ(MΘ
∗ (Π))⊗Q/Z,G O×μ(G),αμ,×μ)
the data consisting of
· MΘ
∗ (Π) — i.e., the projective systems of mono-theta environ-
ments of Propositions 1.2, (i); 1.5, (i);
· (†×θ)(Π) — i.e., “subsets”;
· (†μθ)(Π) — i.e., “splittings”;
58 SHINICHI MOCHIZUKI
· the diagram
Πμ(MΘ
∗ (Π))⊗Q/Z∼
→ Mμ
TM(MΘ
∗ (Π))∼
→ Mμ
TM(Π)
→ M×μ
TM (Π)∼ → O×μ(G) (†μ,×μ)
— where the first “∼
→ ” is the isomorphism determined by the injection of
Remark 1.5.2; the second “∼
→ ” is the isomorphism determined by the ver-
tical arrows of (†×θ)(Π); the “→” is the trivial homomorphism; the final
“ ∼
→ ” denotes the poly-isomorphism induced by the poly-isomorphism
“α×” of Example 1.8, (iii) [cf. also the discussion of “Γ×μ” in Example
1.8, (iv)].
Then this assignment determines a functor R → F which arises from a functo-
rial algorithm; denote the corresponding graph [cf. Example 1.9, (i)] by R†. In
particular, the resulting natural functor ΨR : R → R† [cf. Example 1.9, (i)] is
multiradially defined.
Proof. Assertion (i) follows immediately from the discussion of Remark 1.4.1 and
the references quoted in this discussion. Assertion (ii) follows immediately from the
structure of the objects under consideration, as described in [EtTh], Proposition
1.5, (ii), (iii) [cf. also the proofs of [EtTh], Theorems 1.6, 1.10]. Finally, the
multiradiality of assertion (iii) follows immediately from the characteristic nature
of the various torsion submodules “Mμ
TM(−)” that appear [cf. the discussion of
Remark 1.10.2; the discussion of Remark 1.12.2 below]. ⃝
Remark 1.12.1. One verifies immediately that Corollaries 1.10, 1.11, and 1.12
admit “log-shell versions” [cf. Example 1.8, (ix)]. The various interpretations of
these corollaries discussed in the remarks following the corollaries also apply to such
“log-shell versions”.
Remark 1.12.2.
(i) Modulo the multiradiality of the cyclotomic rigidity isomorphism of Corol-
lary 1.10 [cf. Corollary 1.12, (b)], the essential content of the multiradiality of
Corollary 1.12 lies in
the functorial group-theoretic algorithm implicit in the proof of [EtTh],
Theorem 1.10, (i), for constructing θ(Π) up to a μ2l-indeterminacy—
i.e., asopposedtoonlyuptoa“O×
k -indeterminacy”, asisdoneintheproof
of [EtTh], Theorem 1.6, (iii) — together with the [elementary] observation
that the submodule of [any isomorph of] O×
k constituted by the 2l-torsion
is characteristic [cf. the proof of Corollary 1.12, (iii)].
That is to say, it is this “essential content” that implies that the crucial splittings
(†μθ)(Π) are compatible with gluing together the various collections of coric
data “(G O×μ(G))” that arise from distinct arithmetic holomorphic structures.
(ii) Here, we recall in passing [cf. also the discussion of Remark 1.4.1] that the
functorial group-theoretic algorithm implicit in the proof of [EtTh], Theorem 1.10,
(i), for constructing θ(Π) up to a μ2l-indeterminacy consists of
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 59
normalizingthe´ etalethetafunctionsunderconsiderationbyrequiringthat
theirvalues atpoints[cf. alsothediscussionofRemark1.12.4below]lying
over the 2-torsion point “μ−” of [IUTchI], Example 4.4, (i), be ∈ μ2l
— i.e., of considering´ etale theta functions “of standard type” [cf. [EtTh], Definition
1.9, (ii); [EtTh], Theorem 1.10, (i); [EtTh], Definition 2.7]. Also, we recall from
the proof of [EtTh], Theorem 1.10, (i), that the decomposition groups ⊆ Π corre-
sponding to these points lying over the 2-torsion point “μ−” are reconstructed by
applying, among other tools, the elliptic cuspidalizations reviewed in Proposition
1.6, (ii) [cf. also the discussion of Corollary 2.4, (ii), (b), below].
(iii) By contrast, if, in the context of the discussion of (i), the normalization
reviewed in (ii) consisted of the requirement that certain values of the ´ etale theta
function be equal, for instance, to
2 def = 1+1 ∈ O×
k ⊆ (k×)∧
[where we recall that the residue characteristic of k is assumed to be odd — cf.
[IUTchI], Definition 3.1, (b)], i.e., an element of (k×)∧ whose construction depends,
in an essential way, on the ring structure relative to some specific Θ±ellNF-Hodge
theater — i.e., some specific arithmetic holomorphic structure — then the normal-
ization would fail to give rise to a multiradially defined functor, although [cf.
[AbsTopIII], Corollary 1.10, (h); [IUTchI], Remark 3.1.2] it would nonetheless give
rise to a uniradially defined functor [cf. the discussion of Example 1.9, (iv), (b);
Remark 1.11.5, (ii)].
(iv) From the point of view of the further development of the theory of the
present series of papers, the significance of obtaining “splittings up to a μ-indeter-
minacy” may be summarized as follows. Ultimately, we shall be interested, in
[IUTchIII],inapplyingthetheoryoflog-shellsdevelopedin[AbsTopIII][cf. Remark
1.12.1]. From the point of view of log-shells, which may be thought of as being
contained in O×μ(G), an indeterminacy up to some larger subgroup of O×
k — such
as, for instance, the subgroup generated by 2 = 1 + 1, together with its Aut(G)-
conjugates [cf. the discussion of (iii)] — would imply that
onemayonlywork,inaninconsistentfashion,with[forinstance, theimage
of the log-shell in] the quotient of O×μ(G) by such a larger subgroup
— a situation which is unacceptable from the point of view of the further develop-
ment of the theory of the present series of papers.
(v) The discussion in (i), (ii), and (iii) above of the multiradiality of the
crucial splittings (†μθ)(Π) of Corollary 1.12, (ii), yields another important example
[cf. Remark 1.11.3, (iii)] of the phenomenon that sometimes not only the existence
of a single reconstruction algorithm, but also the content of the reconstruction
algorithm is of crucial importance in the development of the theory. Similar ideas,
relative to the point of view of the theory of [EtTh], may also be seen in the
discussion of [EtTh], Remarks 1.10.2, 1.10.4.
(vi) In general, multiradiality amounts to a sort of “surjectivity” [cf. the defi-
nition of a multiradial environment via a “fullness” condition in Example 1.7, (ii);
60 SHINICHI MOCHIZUKI
the discussion of Example 1.7, (v)] of the radial data onto the coric data. From this
point of view, the content of the multiradiality of the splittings (†μθ)(Π) of Corol-
lary 1.12, (ii), may be thought of as consisting of a splitting of this “surjection of
radial data onto coric data” into
(a) a “purely radial component” constituted by {∞θ(Π)ι/Mμ
TM(Π)},
{∞θ
env(MΘ
∗ (Π))ι/Mμ
TM(MΘ
∗ (Π))} and
(b) a “purely coric component” constituted by M×μ
TM (Π), M×μ
TM (MΘ
∗ (Π))
[cf. the discussion of Remark 1.11.4].
Remark 1.12.3. From the point of view of the discussion of Remark 1.11.3, it
is useful to note that the subsets M×
TM·
∞θ(Π), M×
TM·
∞θ
env(MΘ
∗ (Π)) that appear
in Corollary 1.12 may be thought of as [“roots” of] the images, via the Kummer
map, of a certain generating subset of the monoid of rational functions “O◃
CΘ
(−)”
v
defined in [IUTchI], Example 3.2, (v), which is used to construct the underlying
Frobenioidofthesplit Frobenioid“FΘ
v ”—cf. alsothediscussionofKummerclasses
in [EtTh], Proposition 5.2, (iii). Here, the splittings (†μθ)(Π) of Corollary 1.12, (ii),
correspond to the splitting data of this split Frobenioid FΘ
v . Put another way,
this monoidal data that gives rise to the split Frobenioid
FΘ
v
may be thought of as the result of forgetting the “anabelian struc-
ture” of M×
TM·
∞θ(Π), M×
TM·
∞θ
env(MΘ
∗ (Π)), and (†μθ)(Π)
— cf. the discussion of Remark 1.11.3, (i), (ii); the theory of §3 below, especially,
Proposition 3.4. In particular, the specification of coric data “(G O×μ(G))” in
themultiradialenvironmentthatappearsinCorollary1.12arisesnaturallyfromthe
point of view of applying the “coricity of O×” given in [IUTchI], Corollary 3.7, (iii),
as in the discussion of Remark 1.11.3, (ii). Finally, we recall from the discussion of
Remark 1.11.3, (ii), that this specification of coric data “(G O×μ(G))” has the
eﬀect of inducing, in particular, an (Aut(G),Im(Z×) (⊆ Ism))-indeterminacy on
“G O×μ(G)” [cf. Corollary 1.12, (iii)].
Remark 1.12.4. The fact that the “theta evaluation” functorial algorithm of
Corollary 1.12, (ii), given by restriction to the decomposition groups associated
to the point “μ−
” involves only the topological group “Π” as input data will be
of crucial importance when we combine the theory developed in the present paper
with the theory of log-shells [cf. [AbsTopIII]] in [IUTchIII]. At this point, it is
useful to stop and consider to what extent this sort of “group-theoretic evaluation
algorithm” is an inevitable consequence of various natural conditions. To this end,
let us suppose that we are given some “mysterious evaluation algorithm”
(abstract theta function) → (theta values)
— i.e., which is not necessarily given by restriction to the decomposition group
associated to a closed point. Then [cf. [EtTh], Remark 1.10.4; the theory of the
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 61
“log-wall”, as discussed in [AbsTopIII], §I4] it is natural to require [cf., especially,
the point of view of the discussion of Remark 1.12.3] that this algorithm be
compatible with the operation of forming Kummer classes by extract-
ing N-th roots of the “abstract theta function” and the “theta values”.
In particular, it is natural to require that this algorithm extend to coverings [e.g.,
Galois coverings] on both the input and output data of the algorithm. But then the
natural requirement of functoriality with respect to the Galois groups on either
side leads one [cf. Fig. 1.5 below], in eﬀect, to the conclusion — which we shall
refer to as the principle of Galois evaluation — that
the “mysterious evaluation algorithm” under consideration in fact
arises from a section G → Π¨
Y (Π) of the natural surjection Π¨
Y (Π) G.
Moreover, bythe“Section Conjecture”ofanabeliangeometry, oneexpectsthatsuch
[continuous] sections G → Π¨
Y (Π) necessarily arise from geometric points. [Here,
we pause to observe that this relation to the “Section Conjecture” is interesting in
lightofthediscussionof[IUTchI],Example4.5, (i); [IUTchI],Remark2.5.1.] Inthis
context, it is useful to recall that from the point of view of the theory of [AbsTopIII]
[cf., e.g., the discussion of [AbsTopIII], §I5], the group-theoreticity of the evaluation
algorithm may be thought of as a sort of abstract analogue of the condition, in the
p-adic theory, that an operation involving various Frobenius crystals be compatible
with the Frobenius crystal structures [i.e., connection and Frobenius action] on
the input and output data of the operation.
Π¨
Y (Π)
geometric object
(+ coverings!) that
support(s) the abstract
theta function
- - - >
geometric object
(+ coverings!) that
support(s) the
theta values
G
Fig. 1.5: Theta evaluation and Galois functoriality
Remark 1.12.5.
(i) Recall that the scheme-theoretic Hodge-Arakelov theory reviewed in [HA-
SurI], [HASurII] may be thought of as a sort of scheme-theoretic version of the
well-known classical computation of the Gaussian integral
∞
e−x2
dx= √π
−∞
— i.e., by thinking of the square of this integral as an integral over the cartesian
plane R2, which may be computed easily by applying a coordinate transformation
into polar coordinates. That is to say [cf. the left-hand and middle columns of Fig.
1.6below],themaintheoremofscheme-theoreticHodge-Arakelovtheoryisacertain
comparison isomorphism [cf. [HASurI], Theorem A] between a “de Rham side”—
62 SHINICHI MOCHIZUKI
which consists of certain sections of an ample line bundle on the universal extension
of an elliptic curve — and an“´ etale side” — which consists of arbitrary functions
on the set of l-torsion points of the elliptic curve [where l is, say, some odd prime
number]. Here, the module on the de Rham side is equipped with a natural Hodge
filtration, whilethemoduleonthe´ etalesideisequippedwithanaturalGalois action
byGL2(Fl). Theordered, “step-like” structureoftheHodgefiltrationisreminiscent
of the cartesian structure of the plane R2, i.e., regarded as an ordered collection
[parametrized by one factor of R2] of lines [corresponding to the other factor of R2].
On the other hand, the GL2(Fl)-symmetry of the ´ etale side is reminiscent of the
rotational symmetry of the representation of the Gaussian integral on the plane via
polar coordinates. Moreover, the function “e−x2” itself appears in the Gaussian
poles that appear in the de Rham side [cf. [HASurI], §1.1], while the “√π” may
be thought of as corresponding to the [negative] tensor powers of the sheaf “ω” of
invariant diﬀerentials on the elliptic curve that appear in the subquotients of the
Hodge filtration, which give rise to a Kodaira-Spencer isomorphism [cf. [HASurII],
Theorems 2.8, 2.10] between ω⊗2 and the restriction to the base scheme of the sheaf
of logarithmic diﬀerentials on the moduli stack of elliptic curves — i.e., between ω
and the “square root” of this sheaf of logarithmic diﬀerentials. Finally, we recall
that this relationship between the theory of [HASurI], [HASurII] and the classical
Gaussian integral may be seen more explicitly when this theory is restricted to the
archimedean primes of a number field via the “Hermite model” [cf. [HASurI], §1.1].
classical Gaussian scheme-theoretic inter-universal
integral Hodge-Arakelov theory Teichm¨ uller theory
cartesian coordinates de Rham side, Hodge filtration Frobenius-like structures,
Frobenius-picture
polar coordinates ´ etale side, Galois action on torsion points ´ etale-like structures,
´ etale-picture
Fig. 1.6: Analogy with the classical Gaussian integral
(ii) Just as the theory of [HASurI], [HASurII] may be thought of as a scheme-
theoretic version of the classical theory of the Gaussian integral,
the “inter-universal Teichm¨ uller theory” developed in the present se-
ries of papers may be thought of as a sort of global arithmetic/Galois-
theoretic version of the classical Gaussian integral
— cf. the right-hand column of Fig. 1.6. Indeed, the ordered, “step-like”
nature of the cartesian representation of the Gaussian integral on the plane is remi-
niscent of the structure of the Frobenius-picture discussed in [IUTchI], Corollary
3.8; [IUTchI], Remark 3.8.1 — i.e., in particular, of the notion of a Frobenius-
like mathematical structure that appears in the discussion of [FrdI], Introduction.
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 63
On the other hand, the rotational symmetry of the representation of the Gaussian
integral on the plane via polar coordinates is reminiscent of the´ etale-picture dis-
cussed in [IUTchI], Corollary 3.9, and the following remarks — i.e., in particular,
of the notion of an´ etale-like mathematical structure that appears in the discus-
sion of [FrdI], Introduction. The ´ etale-picture that arises from the multiradially
defined functor of Corollary 1.12 is depicted in Fig. 1.7 below [where we recall the
notation of Proposition 1.4; Example 1.8, (iv)]. From the point of view of the clas-
sical series representation of a theta function — i.e., roughly speaking, the series
“
n∈Z qn2
·Un” [cf. [EtTh], Proposition 1.4] —
this´ etale-picture of various copies of the Gaussian function “qn2” de-
fined on spokes emanating from a single common core
∞θ(iΠ)
...
⏐ ⏐...
∞θ(i′Π) −→
mono-analytic core
G O×μ(G) Ism
←− ∞θ(i′′Π)
... ⏐ ⏐...
∞θ(i′′′Π)
Fig. 1.7: Multiradial ´ etale theta functions
[cf. also the point of view of Remark 1.12.2, (vi)] is highly reminiscent of the polar
coordinate representation of the Gaussian integral on the plane. In this context, it
is also of interest to observe that the coordinate transformation
e−r2
u
that appears in the radial portion of the integrand of the Gaussian integral that
arises from the transformation from cartesian to polar coordinates
2·( e−x2dx)2 = 2· e−x2
−y2 dx dy= e−r2
·2rdr dθ
= d(e−r2) dθ= du dθ
is formally reminiscent of the Θ-link “†Θ
v
→ ‡q
” [cf. [IUTchI], Remark 3.8.1,
v
(i)], various versions of which play a central role in the theory of the present series
of papers.
(iii) Just as the equivalence between cartesian and polar representations of the
classical Gaussian integral is used eﬀectively to compute the value of this Gauss-
ian integral, the relationship between the Frobenius- and´ etale-pictures will play a
central role [cf., especially, the computations of [IUTchIII], §3; [IUTchIV], §1] in
the theory of the present series of papers.
64 SHINICHI MOCHIZUKI
Section 2: Galois-theoretic Theta Evaluation
In the present §2, we develop the theory of group-theoretic algorithms sur-
rounding the Hodge-Arakelov-theoretic evaluation of the ´ etale theta function
on l-torsion points. At a more technical level, this theory depends on a careful
analysis of the issue of conjugate synchronization [cf. Remark 2.6.1] — i.e.,
of synchronizing conjugates of various copies of objects associated to the absolute
Galois group of the base field that occur at the evaluation points — as well as on
the computation, via the theory of [IUTchI], §2, of various conjugacy indetermi-
nacies [cf. Corollaries 2.4, 2.5] that arise from the consideration of certain closed
subgroups of various topological groups. In fact, these various technical issues
arise, ultimately, as a consequence of the requirement of performing the Hodge-
Arakelov-theoretic evaluation in question with respect to a single basepoint [cf.
the discussions of Remark 1.12.4; [IUTchI], Remark 6.12.6]. This Hodge-Arakelov-
theoretic evaluation will play a central role in the theory developed in the present
series of papers.
In the present §2, we shall work mainly with the local portion at v ∈ Vbad of
the various mathematical objects considered in [IUTchI], §3, §4, §5, §6. In fact,
however, many of the constructions carried out in the present §2 will be valid for
strictly local data [as in §1], i.e., that does not necessarily arise from global data
over a number field. Nevertheless, in order to keep the notation simple from the
point of view of discussing the compatibility of the theory of the present §2 with the
theory of [IUTchI], we shall carry out the discussion of the present §2 only for the
localized objects that arise from the theory of [IUTchI], §3, §4, §5, §6, leaving the
routine details of a corresponding purely local theory to the interested reader.
Proposition 2.1. Write
Πtp
¨
Y
(Review of Certain Tempered Coverings) Let v ∈ Vbad
−→ Πtp
Y
−→ Πtp
X
= Πv
v
v
⏐ ⏐ ⏐ ⏐ ⏐ ⏐
−→ Πtp
−→ Πtp
Yv
X
v
.
v
v
Πtp
¨
Yv
for the diagram of open injections of topological groups arising from the theory
of [EtTh], §2 — where
(a) Πtp
X
, Πtp
X
are the tempered fundamental groups determined by the hy-
v
perbolic [orbi]curves Xv, X
v of [IUTchI], Definition 3.1, (e);
(b) Πtp
Y
⊆ Πtp
X
, Πtp
Yv
⊆ Πtp
X
are the open subgroups corresponding to the
v
v
v
tempered coverings Y
→ X
v
v, Yv → Xv determined by the objects “Ylog”,
“Ylog” in the discussion preceding [EtTh], Definition 2.7;
(c) Πtp
¨
Y
⊆ Πtp
X
is the open subgroup determined by the tempered covering
v
¨
Y
v
→ X
v
v of [IUTchI], Example 3.2, (ii); Πtp
¨
Yv
⊆ Πtp
X
v
is the open subgroup
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 65
¨
corresponding to the tempered covering
Yv → Xv determined by the object
“¨
Ylog” in the discussion preceding [EtTh], Lemma 1.2;
(d) the arrows are the natural inclusions, and both squares are cartesian.
Then this diagram may be reconstructed via a functorial group-theoretic algo-
rithm [cf. [EtTh], Proposition 2.4] from the [temp-slim! — cf., e.g., [SemiAnbd],
Example 3.10] topological group Πtp
X
.
v
Proof. The assertions of Proposition 2.1 follow immediately from the results of
[EtTh], [SemiAnbd] that are quoted in the statements of these assertions. ⃝
Remark 2.1.1. In the notation of Proposition 2.1:
¨
(i) Recall that the special fiber of any model of
Yv that arises from a stable
model of Xv consists of a chain of copies of the projective line joined together
at the points “0”, “∞” [cf. the discussion preceding [EtTh], Proposition 1.1]. The
set of irreducible components of this special fiber may be thought of as a torsor
¨
¨
over the group Z. Moreover, the natural action of Gal(
Yv/Yv)∼
= {±1} on
Yv fixes
¨
each of the irreducible components of the special fiber of
Yv and fits into an exact
¨
¨
sequence 1 → Gal(
Yv/Yv) → Gal(
Yv/Xv) → Gal(Yv/Xv) → 1, where Gal(Yv/Xv)
may be identified with the subgroup l·Z ⊆ Z. Since the degree l covering X
→ Xv
v
is totally ramified at the cusps, it thus follows that each of the maps
Γ¨
Y → ΓY ; Γ¨
Y → ΓY ; Γ¨
Y → Γ¨
Y ; ΓY → ΓY ; ΓX → ΓX
on dual graphs associated to the special fibers of stable models [where we omit the
various subscript “v’s” in order to simplify the notation] determined by the various
coverings discussed in Proposition 2.1 induces a bijection on vertices.
(ii) Let ιX, ιX, ι¨
Y be as in Remark 1.4.1, where we take “Xk” to be X
v
¨
ι¨
Y for the automorphism of
Yv induced by ι¨
Y ;
ΓX ⊆ ΓX
for the unique connected subgraph of ΓX which is a tree that is stabilized by ιX and
contains every vertex of ΓX;
Γ•
X ⊆ ΓX
for the unique connected subgraph of ΓX stabilized by ιX that contains precisely one
vertex and no edges. Thus, if one thinks of the vertices of ΓX as being labeled by
elements ∈
{−l ,−l +1,...,−1,0,1,...,l−1,l }
— where the vertex labeled 0 is fixed by ιX — then ΓX is obtained from ΓX by
eliminating the unique edge joining the vertices with labels ±l ; Γ•
X consists of
the unique vertex 0 and no edges. In particular, by taking appropriate connected
. Write
66 SHINICHI MOCHIZUKI
components of inverse images, one concludes [cf. (i)] that ΓX determines finite,
connected subgraphs
Γ•
X ⊆ ΓX ⊆ ΓX, Γ•
¨
Y ⊆ Γ¨
Y ⊆ Γ¨
Y , Γ•
¨
Y ⊆ Γ¨
Y ⊆ Γ¨
Y
¨
¨
of the dual graphs corresponding to X
v,
Yv,
Y
which are stabilized by the respec-
v
tive “inversion automorphisms” ιX, ι¨
Y , ι¨
Y . Here, each subgraph Γ•
(−) consists of
precisely one vertex and no edges, while the set of vertices of each subgraph Γ(−)
maps bijectively to the set of vertices of ΓX. In fact, [although we shall not use this
fact in the present series of papers] it is not diﬃcult to verify, by considering the
divisibility at the edges [i.e., nodes] of the divisor of poles of the theta function [cf.
[EtTh], Proposition 1.4, (i)], that
each subgraph Γ(−) maps isomorphically to ΓX.
Proposition 2.2. the notation of Proposition 2.1, write
(Decomposition Groups Associated to Subgraphs) In
Πv• ⊆ Πv ⊆ Πv
for the decomposition groups determined, respectively, by the subgraphs Γ•
X and
ΓX — i.e., more precisely, the group “Πtp
X,H” of [IUTchI], Corollary 2.3, (iii),
where we take “X” to be X
v, “H” to be Γ•
X or ΓX, “Σ” to be {l}, and “Σ” to be
Primes. Thus, Πv is well-defined up to Πv-conjugacy; once one fixes Πv , then
the subgroup Πv• ⊆ Πv is well-defined up to Πv -conjugacy [cf. Remark 2.2.1
below]; Πv ⊆ Πtp
Yv
Πv = Πtp
Y
. Note, moreover, that we may assume that Πv•,
v
def
Πv , and ι
= ι¨
Y [cf. Remarks 1.4.1, (ii); 2.1.1, (ii)] have been chosen so that
some representative of ι stabilizes Πv• and Πv . Then:
(i) The collection of data (Πv• ⊆ Πv ⊆ Πv,ι), regarded up to Πv-conjugacy,
may be reconstructed via a functorial group-theoretic algorithm from the topo-
logical group Πv.
(ii) The functorial group-theoretic algorithms
Πv → θ(Πv) ⊆ ∞θ(Πv) ⊆ lim
− →
J
H1(Π¨
Y (Πv)|J,(l·ΔΘ)(Πv))
of Proposition 1.4 [i.e., where we take “Π” to be Πv], together with the condition of
invariance with respect to ι [cf. [EtTh], Proposition 1.4, (ii); the proof of [EtTh],
Theorem 1.6, (iii)], determines a specific μ2l- (respectively, μ (= Mμ
TM(Πv))-)
orbit
θι(Πv) ⊆ θ(Πv) (respectively,∞θι(Πv) ⊆ ∞θ(Πv))
within the unique {(l·Z)×μ2l}- (respectively, each {(l·Z)×μ}-) orbit contained
in the set θ(Πv) (respectively,∞θ(Πv)) [cf. Proposition 1.4; Corollary 1.12, (ii)].
def
=
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 67
Proof. Assertion (i) follows immediately from the fact that dual graphs of stable
models may be reconstructed via a functorial group-theoretic algorithm from the
corresponding tempered fundamental group [cf., e.g., [SemiAnbd], Corollary 3.11,
or, alternatively, [AbsTopI], Theorem 2.14, (i)]. Assertion (ii) follows immediately
from the results of [EtTh] that are quoted in the statements of assertion (ii). ⃝
Remark 2.2.1. In the notation of Proposition 2.2, we recall that since the
subgroup Πv ⊆ Πv is commensurably terminal [cf. [IUTchI], Corollary 2.3, (iv)],
it follows that even when this subgroup is subject to a Πv-conjugacy indeterminacy,
the indeterminacy induced on any specific Πv-conjugate of this subgroup Πv is
an indeterminacy with respect to inner automorphisms [i.e., of the specific Πv-
conjugate of Πv ].
Definition 2.3.
(i) In the notation of Proposition 2.2; [IUTchI], Definition 3.1, (e); [IUTchI],
Remark 3.1.1: Write Δv
def = Δtp
, Δ±
def = Δtp
, Π±
def = Πtp
, Δcor
def = Δtp
X
v
X
v
X
v
Cv, Πcor
v
v
v
v
Πtp
Cv; denote the respective profinite completions by means of a “∧”. Thus, we have
natural diagrams of outer inclusions of topological groups
Δv −→ Δ±
v −→ Δcor
v
⏐ ⏐ ⏐ ⏐ ⏐ ⏐
Πv −→ Π±
v −→ Πcor
v
Δv −→ Δ±
v −→ Δcor
v
⏐ ⏐ ⏐ ⏐ ⏐ ⏐
Πv −→ Π±
v −→ Πcor
v
— where the left-hand diagram admits a natural outer inclusion into the right-
hand diagram, in the evident fashion. Here, we recall that Δv includes as a normal
open subgroup of Δ±
v of index l [cf. [EtTh], Proposition 2.2, (ii); [EtTh], Remark
2.6.1], that Δ±
v includes as a normal open subgroup of Δcor
v of index 2l [cf. the
discussion preceding [EtTh], Definition 2.1], and that Π±
v and Πcor
v may be recon-
structed group-theoretically from Πv [cf. [EtTh], Proposition 2.4]. We shall use
these diagrams to regard the various groups appearing in the diagrams as sub-
groups, well-defined up to Πcor
v -conjugacy, of Πcor
v . Recall the collection of data
Write
(Πv• ⊆ Πv ⊆ Πv,ι), well-defined up to Πv-conjugacy, of Proposition 2.2, (i).
Π±
v•
def
= NΠ±
v (Πv•) ⊆ Π±
v
def
= NΠ±
v (Πv ) ⊆ Π±
v
[cf. Remark 2.1.1, (ii); [IUTchI], Corollary 2.3, (iv)] — so we have natural isomor-
phisms
Π±
v•/Πv•
∼
→ Π±
v /Πv
∼
→ Π±
v /Πv
∼
→ Δ±
v /Δv
∼
→ Gal(X
v/Xv) (∼
= Z/lZ)
and equalities Π±
v• Πv = Πv•, Π±
v Πv = Πv [cf. [IUTchI], Corollary 2.3, (iv)].
(ii) Let Π⊇, Π⊆ be any of the topological groups Πv, Π±
v , Πcor
v , Πv, Π±
v , Πcor
v of
(i); suppose that Π⊆ ⊆ Π⊇ relative to one of the natural outer inclusions discussed
68 SHINICHI MOCHIZUKI
in (i). Then we recall that the cuspidal inertia groups of Π⊇ may be reconstructed
group-theoretically from the topological group Π⊇ via the algorithms of [AbsTopI],
Lemma 4.5 [cf. also [IUTchI], Remark 1.2.2, (ii)]; [AbsTopI], Proposition 4.10, (vi),
and that the cuspidal inertia groups of Π⊆ may be obtained as the intersections
with Π⊆ of those cuspidal inertia groups of Π⊇ that contain a finite index subgroup
that lies inside Π⊆ [cf. [IUTchI], Corollary 2.5; [IUTchI], Remark 2.5.2], while
the cuspidal inertia groups of Π⊇ may be obtained as the Π⊇-conjugates of the
commensurators [or, alternatively, the normalizers] in Π⊇ of the cuspidal inertia
groups of Π⊆ [cf. [CombGC], Proposition 1.2, (ii)].
(iii) Let Π⊆ be any of the topological groups Πv, Π±
v , Πv, Π±
v of (i); if Π⊆
is equal to Πv or Π±
v , then set Π⊇
def = Π±
v ; if Π⊆ is equal to Πv or Π±
v , then set
def
Π⊇
= Π±
v . Thus, Π⊆ ⊆ Π⊇. Then [cf. [IUTchI], Definition 6.1, (iii)] we define
a ±-label class of cusps of Π⊆ to be the set of Π⊆-conjugacy classes of cuspidal
inertia subgroups of Π⊆ whose commensurators in Π⊇ [cf. the discussion of (ii)]
determine a single Π⊇-conjugacy class of subgroups in Π⊇. [Here, we remark in
passing that since the inclusion Π⊆ ⊆ Π⊇ corresponds to a totally ramified covering
of curves, it is not diﬃcult to verify that such a set of Π⊆-conjugacy classes is, in
fact, of cardinality one.] Write
LabCusp±(Π⊆)
for the set of ±-label classes of cusps of Π⊆. Thus, when Π⊆ = Πv, if we set †Dv
def
=
Btemp(Π⊆)0, then the set LabCusp±(Π⊆) may be naturally identified with the set
LabCusp±(†Dv) of [IUTchI], Definition 6.1, (iii). In particular, LabCusp±(Πv) =
LabCusp±(†Dv) admits a natural action by F×
l , as well as a zero element
†η0
v
∈ LabCusp±(Πv) = LabCusp±(†Dv)
and a ±-canonical element
†η±
v
∈ LabCusp±(Πv) = LabCusp±(†Dv)
— well-defined up to multiplication by ±1, which may be constructed solely from
†Dv [cf. [IUTchI], Definition 6.1, (iii)].
(iv) Let t ∈ LabCusp±(Πv). Then t determines a unique vertex of ΓX [cf.
[CombGC], Proposition 1.5, (i)]. Write Γ•t
X ⊆ ΓX for the connected subgraph with
no edges whose unique vertex is the vertex determined by t. Then just as in the
case of Γ•
X [i.e., the case where t is the zero element] discussed in Proposition
2.2, the subgraph Γ•t
X determines — via a functorial group-theoretic algorithm — a
decomposition group
Πv•t ⊆ Πv ⊆ Πv
— which is well-defined up to Πv -conjugacy. Finally, we shall write Π±
def
=
v•t
NΠ±
v (Πv•t)[cf. (i)]; thus,wehaveanaturalisomorphismΠ±
v•t/Πv•t
∼
→Gal(X
v/Xv).
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 69
(v) Let Π⊆ be either of the topological groups Π±
v , Π±
v of (i); if Π⊆ = Π±
v , then
set Π⊇
def = Πcor
v ; if Π⊆= Π±
def
v , then set Π⊇
= Πcor
v . Then one verifies immediately
that the images [via the natural outer injection Πv → Π⊆] in LabCusp±(Π⊆) of
the various structures on LabCusp±(Πv) reviewed in (iii) determine [in the notation
and terminology of [IUTchI], Definition 6.1, (i)] a natural F±
l -torsor structure on
LabCusp±(Π⊆). Moreover, the natural action of Π⊇/Π⊆ on Π⊆ preserves this
F±
l -torsor structure, hence determines a natural outer isomorphism
Π⊇/Π⊆
∼
→ F ±
l
[cf. [IUTchI], Definition 6.1, (i)].
Remark 2.3.1. In the situation of (iii), suppose that the inclusion Π⊆ ⊆ Π⊇ is
strict. Then one verifies immediately that if I ⊆ Π⊇ is a cuspidal inertia group of
Π⊇, then the cuspidal inertia group I Π⊆ ⊆ Π⊆ of Π⊆ satisfies
I Π⊆= Il
— where the superscript l is relative to the group operation on I, written multi-
plicatively. In particular, [even though Πv (respectively, Πv) fails to be normal in
Πcor
v (respectively, Πcor
v )] it follows — since Π±
v (respectively, Π±
v ) is normal in Πcor
v
(respectively, Πcor
v ) — that the cuspidal inertia groups of Πv (respectively, Πv) are
permuted by the conjugation action of Πcor
v (respectively, Πcor
v ).
The theta evaluation algorithm discussed in the following Corollaries 2.4, 2.5,
2.8, and 2.9 is central to the theory of the present §2, and, indeed, of the present
series of papers.
Corollary 2.4. (F ±
l -Symmetric Two-torsion Translates of Cusps) In
the notation of Definition 2.3: Let t ∈ LabCusp±(Πv); ∈ {•t, }. Write
Δv
def = Δv Πv , Δ±
def = Δ±
v
v Π±
v
Π
v¨
def = Πv Πtp
¨
Y
, Δ
v¨
def = Δv Π
v¨
v
— so we have
[Πv : Π
v¨] = [Δv : Δ
v¨] = 2, [Π±
v
[Π±
v
: Π
v¨] = [Δ±
v
: Πv ] = [Δ±
v
: Δv ] = l
: Δ
v¨] = 2l
[cf. Definition 2.3, (i), (iv)].
(i) (Inclusions and Conjugates) Let It ⊆ Πv be a cuspidal inertia group
that belongs to the class determined by t such that It ⊆ Δv . Consider the [Π±
v-
conjugacy stable] sets of subgroups of Π±
v
{Iγ1
t }γ1∈Π±
v
= {Iγ1
t }γ1∈Δ±
v
70 SHINICHI MOCHIZUKI
{Πγ2
v }γ2∈Π±
= {Πγ2
v
v }γ2∈Δ±
; {(Π±
v
v )γ3}γ3∈Π±
= {(Π±
v
v )γ3}γ3∈Δ±
v
— where the superscript “γ’s” denotes conjugation [i.e., “(−) → γ·(−)·γ−1”] by
γ. Then for γ,γ′ ∈ Δ±
v , the following three conditions are equivalent:
′
′
(a) γ′ ∈ Δ±
v ; (b) Iγ·γ
t ⊆ Πγ
v ; (c) Iγ·γ
t ⊆ (Π±
v )γ
.
(ii) (Two-torsion Translates of Cusps) In the situation of (i), if we write
δ def
= γ·γ′ ∈ Δ±
v , then any inclusion
′
Iδ
t = Iγ·γ
t ⊆ Πγ
v
= Πδ
v
as in (i) completely determines the following data:
(a) a decomposition group Dδ
t
inertia group Iδ
t ;
def
= NΠδ
v(Iδ
t ) ⊆ Πδ
v¨ corresponding to the
(b) a decomposition group Dδ
⊆ Πδ
μ−
v¨, well-defined up to (Π±
v )δ- [or,
equivalently, (Δ±
v )δ-] conjugacy, corresponding to the torsion point “μ−
”
of Remark 1.4.1, (i), (ii), via the algorithms of [SemiAnbd], Theorem
6.8, (iii) [concerning the group-theoreticity of the decomposition groups
of torsion points], and [SemiAnbd], Corollary 3.11 [concerning the dual
semi-graphs of the special fibers of stable models], applied to Δδ
v ⊆ Πδ
v;
(c) a decomposition group Dδ
t,μ−
⊆ Πδ
v¨, well-defined up to (Π±
v )δ
-
[or, equivalently, (Δ±
v )δ-] conjugacy — i.e., the image of an evaluation
section [cf. [IUTchI], Example 4.4, (i)] — corresponding to the “μ−
-
translate of the cusp that gives rise to Iδ
t ”, via the algorithm of [SemiAnbd],
Theorem 6.8, (iii) [concerning the group-theoreticity of the decomposition
groups of translates by torsion points of the cusps].
Moreover, the construction of the above data is compatible with conjugation by
arbitrary δ ∈ Δ±
v , as well as with the natural inclusion Πv•t ⊆ Πv of Definition
2.3, (iv), as one varies ∈ {•t, }.
(iii) (F ±
l -Symmetry) Suppose that= •t. Then the construction of the
data of (ii), (a), (c), is compatible with conjugation by arbitrary δ ∈ Πcor
v [cf.
Remark 2.3.1]. Here, we recall from Definition 2.3, (v), that we have natural outer
isomorphisms Δcor
v /Δ±
∼
→ Πcor
v
v /Π±
∼
→ F ±
v
l.
Proof. First, we consider assertion (i). The implications (a) =⇒ (b) and (b) =⇒
(c) are immediate from the definitions [cf. also Remark 2.3.1]. Thus, it suﬃces to
′
verifythat(c)=⇒(a), i.e., thattheconditionIγ·γ
t ⊆ (Π±
v )γ impliesthatγ′ ∈ Δ±
v ;
we may assume without loss of generality that γ = 1. Then by [IUTchI], Corollary
′
2.5 [cf. also [IUTchI], Remark 2.5.2], the inclusion Iγ
t ⊆ Π±
v ⊆ Π±
v implies that
γ′ ∈ Δ±
v . Now, by applying the equivalence of [IUTchI], Corollary 2.3, (vi) [cf.
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 71
also [CombGC], Proposition 1.2, (ii)], to the various finite index open subgroups
of Δ±
v , it follows that γ′ ∈ Δ±
— where we use the notation “∧” to denote the
v
closure in Δ±
v [cf. Proposition 2.2; Definition 2.3, (iv); [IUTchI], Corollary 2.3,
(ii)] — hence that γ′ ∈ Δ±
= Δ±
v
v
Δ±
v [cf. [IUTchI], Corollary 2.3, (v)]. This
completes the proof of assertion (i). Assertions (ii) and (iii) follow immediately
from the definitions and the references quoted in the statements of these assertions.
⃝
Remark 2.4.1. Note that by applying [IUTchI], Proposition 2.4, (i) [cf. the
proof of [IUTchI], Corollary 2.5; [IUTchI], Remark 2.5.2], one may replace “It” in
Corollary 2.4 by its maximal pro-l′ subgroup for any l′ ∈ Primes \{pv}. The use of
such maximal pro-l′ subgroups sometimes results in a simplification of arguments
involving intersections with other closed subgroups, since every closed subgroup of
such a maximal pro-l′ subgroup is either open or trivial.
Corollary 2.5. Corollary 2.4:
(Group-theoretic Theta Evaluation) In the notation of
(i) (Restriction of Subquotients to Subgraphs) Write
(l·ΔΘ)(Πv¨)
for the subquotient of Πv¨ determined by the subquotient (l·ΔΘ)(Πv) of Πv. Then
the inclusion Πv¨ → Πv induces an isomorphism (l·ΔΘ)(Πv¨)∼
→ (l·ΔΘ)(Πv).
Write
Πv Gv(Πv), Πv¨ Gv(Πv¨)
for the quotients determined by the natural surjection Πv Gv. Then there exists
a functorial group-theoretic algorithm for constructing these quotients from
the topological group Πv [cf., e.g., [AbsAnab], Lemma 1.3.8, as well as Proposition
2.2, (i); Corollary 2.4 of the present paper].
´
(ii) (Restriction of
tion Points) Let
Etale Theta Functions to Subgraphs and Evalua-
′
Iδ
t = Iγ·γ
t ⊆ Πδ
v¨ ⊆ Πγ
v = Πδ
v
be an inclusion as in Corollary 2.4, (ii) [where we take def
= ]. Then restriction
of the ιγ-invariant sets θι(Πγ
v), ∞θι(Πγ
v) of Proposition 2.2, (ii), to the subgroup
Πγ
v¨ ⊆ Π¨
Y (Πγ
v) (⊆ Πγ
v) yields μ2l-, μ-orbits of elements
θι(Πγ
v¨) ⊆ ∞θι(Πγ
v¨) ⊆ lim
− →
J
H1(Πγ
v¨|J,(l·ΔΘ)(Πγ
v¨))
— where J ⊆ Πv ranges over the open subgroups of Πv — which, upon further
restriction to the decomposition groups Dδ
t,μ− of Corollary 2.4, (ii), (c), yield
μ2l-, μ-orbits of elements
θt(Πγ
v¨) ⊆ ∞θt(Πγ
v¨) ⊆ lim
− →
JG
H1(Gv(Πγ
v¨)|JG,(l·ΔΘ)(Πγ
v¨))
72 SHINICHI MOCHIZUKI
for each t ∈ LabCusp±(Πγ
v)∼
→ LabCusp±(Πv) — where JG ⊆ Gv(Πγ
v¨) ranges over
the open subgroups of Gv(Πγ
v¨); the “∼
→ ” is induced by conjugation by γ. Moreover,
the sets θt(Πγ
v¨), ∞θt(Πγ
v¨) depend only on the label |t| ∈ |Fl| determined by t [cf.
Definition 2.3, (iii); [IUTchI], Example 4.4, (i); [IUTchI], Definition 6.1, (iii)].
Thus, we shall write θ|t|(Πγ
v¨) def
= θt(Πγ
v¨), ∞θ|t|(Πγ
v¨) def
= ∞θt(Πγ
v¨).
(iii) (Functorial Group-theoretic Evaluation Algorithm) If one starts
with an arbitrary Δ±
v -conjugate Πγ
v¨ of Πv¨, and one considers, as t ranges
over the elements of LabCusp±(Πγ
v)∼
→ LabCusp±(Πv) [where the “∼
→ ” is induced
by conjugation by γ], the resulting μ2l-, μ-orbits θ|t|(Πγ
v¨), ∞θ|t|(Πγ
v¨) arising from
an arbitrary Δ±
v -conjugate Iδ
t of It that is contained in Πγ
v¨ [cf. (ii)], then one
obtains a group-theoretic algorithm for constructing the collections of μ2l-, μ-
orbits
{θ|t|(Πγ
v¨)}|t|∈|Fl|; {∞θ|t|(Πγ
v¨)}|t|∈|Fl|
which is functorial in the topological group Πv and, moreover, compatible with
the independent conjugacy actions of Δ±
v on the sets {Iγ1
t }γ1∈Π±
= {Iγ1
v
t }γ1∈Δ±
v
and {Πγ2
v¨}γ2∈Π±
= {Πγ2
v
v¨}γ2∈Δ±
[cf. the sets of Corollary 2.4, (i); Remark 2.2.1].
v
Proof. Assertions (i), (ii), and (iii) follow immediately from the definitions and
the references quoted in the statements of these assertions. Here, in assertion
(i), we observe that the fact that the inclusion Πv¨ → Πv induces an isomorphism
(l·ΔΘ)(Πv¨)∼
→ (l·ΔΘ)(Πv) follows immediately by considering the cuspidal inertia
groups involved. ⃝
Remark 2.5.1.
(i) Recall from the discussion of [IUTchI], Example 4.4, (i), that relative to the
“standard” cyclotomic rigidity isomorphism (∗bs-Gal) of Proposition 1.3, (ii), and
the resulting Kummer map
K×
v → H1(Gv(Πv¨),(l·ΔΘ)(Πv¨))
j ∈ |Fl|, the set θj(Πv¨) consists of precisely the μ2l-orbit of the “theta value”
[i.e.,wetake“δ”inCorollary2.5,(ii), tobetheidentity—withoutlossofgenerality,
in light of Remark 2.2.1], it follows immediately from the definition of the connected
subgraph “ΓX” in Remark 2.1.1, (ii) [cf. also [IUTchI], Corollary 2.3, (vi)], that, for
j2
q
v
[cf. [IUTchI], Example 3.2, (iv); [EtTh], Proposition 1.4, (ii)] — where the “j” in
the exponent denotes the element ∈ {0,1,...,l } determined by the given element
j ∈ |Fl|.
1
2(n+1
2)2
·q
X·
¨
U2n+1
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 73
(ii) Note that [the reciprocals of the l-th powers of] the theta values discussed
in (i) are somewhat unusual among the various values
¨
Θ(c)
— where c ∈ Kv — attained by the theta series
¨
Θ =
¨
¨
Θ(
U) def
1
= q−
8
X·
n∈Z
(−1)n
discussed in [EtTh], Proposition 1.4 [cf. the notation of loc. cit.] in that they
satisfy the following crucial property [cf. the discussion of Remark 1.12.2]:
the ratio¨
¨
Θ(c)/
Θ(c′) is a root of unity, for any c′ ∈ Kv [corresponding
¨
to a point of
Yv] that occurs as the result of applying an automorphism of
¨
Πv to [the point of
Yv that corresponds to] c such that c′/c is a unit.
That is to say, the reciprocals of the l-th powers of the theta values discussed in (i)
¨
j/2
correspond to the values
Θ(±√−1·q
X ), where j ∈ {0,1,...,l }, i.e., the values
j/2
at points separated by periods [i.e., the “q
X ”] from the point “±√−1”. These
values may be computed easily from the “functional equations” given in [EtTh],
Proposition 1.4, (ii).
(iii) Note that, in the context of the F ±
l -symmetry discussed in Corollary
2.4, (iii),
the various μ2l-multiple indeterminacies that occur, for various j ∈ |Fl|,
in the μ2l-orbit θj(Πv¨) are independent.
That is to say, these indeterminacies are not “synchronized” so as to arise from a
single indeterminacy that is independent of j. Indeed, each of these μ2l-multiple
indeterminacies arises as a consequence of the action of (Δ±
v•t/Δv¨
•t)δ, where we
recall from Corollary 2.4 that [Δ±
v•t : Δv¨
•t] = 2l, on the decomposition groups
“Dδ
t,μ−
⊆ Πδ
v¨” of Corollary 2.4, (ii), (c), hence is induced by the Δ±
v -outer nature
of the action of Δcor
v /Δ±
∼
→ F ±
v
l that appears in Corollary 2.4, (iii) — cf. the
discussion of Remarks 2.5.2, 2.6.2 below.
Remark 2.5.2.
(i) If one thinks of the
“set {Iγ1
t }γ1∈Π±
= {Iγ1
v
t }γ1∈Δ±
v
(respectively, “set {Πγ2
v¨}γ2∈Π±
= {Πγ2
v
v¨}γ2∈Δ±
regarded up to Δ±
v -conjugacy”
regarded up to Δ±
v -conjugacy”)
v
[cf. Corollary 2.5, (iii)] as a sort of quotient by Δ±
v , then one may think of the
various inclusion morphisms Iγ1
t → Πγ2
v¨ as a sort of morphism between quotients
Δ±
v {Iγ1
t }γ1∈Δ±
v
/Δ±
v → Δ±
v {Πγ2
v¨}γ2∈Δ±
v
/Δ±
v
/Δ±
v
74 SHINICHI MOCHIZUKI
which induces a morphism between quotients
Δ±
v {Dγ1
t,μ−}γ1∈Δ±
v
/Δ±
v → Δ±
v {Πγ2
v¨}γ2∈Δ±
v
—cf. Corollary2.4, (ii); thediscussionof[IUTchI],Remark4.5.1, (i), (iii). Sinceall
of the inclusions involved occur within a single “ambient container” — namely,
Π±
v ,regardeduptoΠ±
v -conjugacy—theevaluation algorithmdiscussedinCorollary
2.5, (iii), may be thought of as a sort of “nested” version of the principle of
“Galois evaluation” discussed in Remark 1.12.4. Here, we note that unlike the
situation discussed in Remark 1.12.4, in which the subgroup Π¨
Y (Π) ⊆ Π is normal,
the subgroups Πv ,Πv¨ ⊆ Π±
v are far from being normal!
(ii) In the notation of [IUTchI], Definition 3.1, (d) [cf. also the notation of
[IUTchI], Definition 6.1, (v)], write
Π ± def = ΠXK ; Δ ± def = ΔX
— so Δ ± may be naturally identified, up to inner automorphism, with Δ±
v . Then
note that unlike the tempered fundamental groups Δv, Δ±
v , Δv , Δv¨ or the local
Galois groups Πv/Δv, Π±
v /Δ±
v , Πv /Δv , Πv¨/Δv¨ — all of which depend, in a
quite essential way, on v — the topological group Δ ± ∼
= Δ±
v is independent of
v and, moreover, may be recovered directly from the global portion“†D ±” of
a D-Θell-bridge [cf. [IUTchI], Definition 6.4, (ii); [AbsAnab], Lemma 1.1.4, (i)].
On the other hand, Δ ± ∼
= Δ±
v also serves as an “ambient container” for the
Δ±
v -conjugates of both It and Δv¨. That is to say,
Δ ± (∼
= Δ±
v ) serves as a sort of “common bridge” between local data
[such as Δv¨] and global data such as the labels
t ∈ LabCusp±(Π ±) (∼
→ LabCusp±(Πγ
v)∼
→ LabCusp±(Πv))
[wherewewriteLabCusp±(Π ±) def = LabCusp±(B(Π ±)0)—cf. [IUTchI],
Definition 6.1, (vi)], in the form of conjugacy classes of It.
(iii) On the other hand, if, in the discussion of (ii), one passes — as in the
theory of [IUTchI], §6 — between distinct v via this “global bridge” Δ ±, then
one must take into account the fact that, unlike the labels t [i.e., conjugacy classes
of It], the groups Πv¨ do not admit globalizations or extensions to multiple v’s.
This is precisely the reason for
the independence of the Δ±
v (∼
= Δ ±)- [or, equivalently, Π±
v -] conjugacy
indeterminacies that act on the conjugates of It and Πv¨
[cf. the “quotient interpretation” of (i) above; the statement of Corollary 2.5, (iii)].
Here, we observe that since [in the notation of [IUTchI], Definition 3.1] neither of
the natural surjections Π±
v Gv, Π ± GK admits a section that simultaneously
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 75
normalizes the subgroups It, as t ranges over the elements of LabCusp±(Π ±)∼
→
LabCusp±(Πγ
v)∼
→ LabCusp±(Πv) [cf., e.g., [AbsSect], Theorem 1.3, (ii); [pGC],
Theorem C], it follows that any Gv- (respectively, GK-) conjugacy indeterminacy
necessarily results in a Δ±
∼
v
= Δ ±-conjugacy indeterminacy acting on the various
It, i.e.,
∼
= Δ ±-conjugacy indeterminacies on the subgroups It,
Gv-conjugacy indeterminacy=⇒ Δ±
v -conjugacy indeterminacy,
GK-conjugacy indeterminacy=⇒ Δ ±-conjugacy indeterminacy.
Since, moreover, the natural surjection Δcor
v Δcor
v /Δ±
v does not admit a splitting,
it follows that the Δ±
v -outer action of Δcor
v /Δ±
∼
→ F ±
v
l of Corollary 2.4, (iii),
induces
independent Δ±
v
for distinct t.
Inasimilarvein,sinceGv does not determine a direct summandofGK —cf. [NSW],
Corollary 12.1.3; the phenomenon of the non-splitting of “prime decomposition
trees” discussed in [IUTchI], Remark 4.3.1, (ii) — it follows that any GK-conjugacy
indeterminacy[which,asjustdiscussed,givesrisetoΔ ±-conjugacyindeterminacy]
induces independent Gv-conjugacy indeterminacies on the various GK-conjugates
of Gv [hence also, as just discussed, independent Δ±
v -conjugacy indeterminacies] —
i.e.,
GK-conjugacy indeterminacy=⇒ independent Gv-conjugacy indeterminacies
— cf. the discussion of [IUTchI], Remark 4.5.1, (iii).
(iv) One way to visualize the independent conjugacy indeterminacies of the
discussion of (iii) above is via the illustration given in Fig. 2.1 below.
... ◦ ◦ ◦ ◦ ◦ ...
... • −→ • −→ • −→ • −→ •...
Fig. 2.1: Independent conjugacy indeterminacies
That is to say, one thinks of the upper and lower lines of Fig. 2.1 as being equipped
with independent actions by groups of horizontal translations [i.e., each of which
is isomorphic to Z]; one thinks of each of the “◦’s” in the upper line as representing
a Δ ± ∼
= Δ±
v -conjugate of It and of each of the “• −→ •’s” in the lower line as
representing a Δ ± ∼
= Δ±
v -conjugate of Πv¨. Thus, since the translation actions on
the upper and lower lines are not synchronized with one another [cf. the discussion
of (iii)],
there is no way to separate — i.e., in a fashion that is compatible with
the indeterminacy arising from both translation actions — the inclusion
of a “◦” into a “• −→ •” as the left-hand “•” from the inclusion of the
same “◦” into some “• −→ •” as the right-hand“•”.
76 SHINICHI MOCHIZUKI
Corollary 2.6. lary 2.5, (ii):
(Splittings Defined on Subgraphs) In the notation of Corol-
(i) (“M×
TM” Defined on Subgraphs) The γ-conjugate of the quotient Πv¨
Gv(Πv¨) of Corollary 2.5, (i), determines subsets
lim
− →
H1(JG,(l·ΔΘ)(Πγ
v¨)) ⊇ M×
TM(Πγ
v¨) ⊆ lim
− →
H1(Πγ
v¨|J,(l·ΔΘ)(Πγ
v¨)),
JG
J
M×
TM·θι(Πγ
v¨) ⊆ M×
TM·
∞θι(Πγ
v¨) ⊆ lim
− →
H1(Πγ
v¨|J,(l·ΔΘ)(Πγ
v¨))
J
— where JG ⊆ Gv(Πv¨), J ⊆ Πv range over the open subgroups of Gv(Πv¨), Πv,
respectively; M×
TM·θι(−) def
= M×
TM(−)· θι(−), M×
TM·
∞θι(−) def
= M×
TM(−)·
∞θι(−)
— which are compatible, relative to the first restriction operation discussed
in Corollary 2.5, (ii), with the corresponding subsets “M×
TM(−)”, “M×
TM·θι(−)”,
“M×
TM·
∞θι(−)” of Proposition 1.4 and Corollary 1.12 [cf. Corollary 1.12, (a), (c),
(e); Corollary 1.12, (i); Remark 1.11.5, (i), (ii)]. Also, [cf. Corollary 1.12] let us
write
M×μ
TM (Πγ
v¨) def
= M×
TM(Πγ
v¨)/Mμ
TM(Πγ
v¨)
— where Mμ
TM(Πγ
v¨) ⊆ M×
TM(Πγ
v¨) denotes the submodule of torsion elements.
(ii) (Splittings at Zero-labeled Evaluation Points) In the situation of
Corollary 2.5, (ii), suppose that t is taken to be the zero element. Then the
set θt(Πγ
v¨) (respectively,∞θt(Πγ
v¨)) is equal to the μ2l- (respectively, μ-) orbit of
the identity element [i.e., the zero element of cohomology module in question, if
one denotes the module structure additively]. In particular, if one considers the
quotient of the diagram of the first display of (i) by Mμ
TM(Πγ
v¨), then restriction
to the decomposition groups Dδ
t,μ− of Corollary 2.4, (ii), (c), determines splittings
M×μ
TM (Πγ
v¨)×{∞θι(Πγ
v¨)/Mμ
TM(Πγ
v¨)}
of M×
TM·
∞θι(Πγ
v¨)/Mμ
TM(Πγ
v¨) which are compatible, relative to the first restric-
tion operation discussed in Corollary 2.5, (ii), with the splittings of Corollary
1.12, (ii).
Proof. Assertions (i) and (ii) follow immediately from the definitions and the
references quoted in the statements of these assertions. ⃝
Remark 2.6.1.
(i) One of the most central properties, from the point of view of the theory
of the present series of papers, of the evaluation algorithm of Corollary 2.5, (iii),
consists of the observation that this algorithm is performed
relativetoasingle basepoint —i.e.,fromamoregeometricpointofview,
relative to the “fundamental group” Πγ
v¨ corresponding to the connected
subgraph ΓX ⊆ ΓX [cf. Remark 2.1.1, (ii)].
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 77
In particular, despite the fact that we are ultimately interested in [not a single, but
rather] a plurality of theta values, associated to the various |t| ∈ |Fl|, these theta
values
θ|t|(Πγ
v¨) ⊆ H1(Gv(Πγ
v¨),(l·ΔΘ)(Πγ
v¨))
for various |t| ∈ |Fl| are all computed relative to the single copy [i.e., which
is independent of |t|!] of the Galois group Gv(Πγ
v¨) and the single cyclotome
(l· ΔΘ)(Πγ
v¨) [i.e., which is independent of |t|!] arising from Πγ
v¨ — i.e., arising
from the “single basepoint” under consideration. We shall refer to this phenom-
enon by the term conjugate synchronization. This conjugate synchronization
is necessary in order to perform Kummer theory [cf. the discussion of Galois
evaluation in Remark 1.12.4], as we shall do in §3.
(ii) Put another way, the significance of conjugate synchronization in the con-
text of Kummer theory — especially, in the context of the theory of Gaussian
Frobenioids, to be developed in §3 below — may be understood as arising from
the requirement that the collection of theta values, for |t| ∈ Fl , be treated as
a single unified entity, whose Kummer theory may be described by
considering the action of a single Galois group in the context of the
simultaneous extraction of N-th roots of all theta values, relative to a
single cyclotome [i.e., copy of the module of N-th roots of unity] that
acts simultaneously on the N-th roots of all of the theta values, and in a
fashion that is compatible with the Kummer theory of the “base field”
[i.e., arising from the quotient Πγ
v¨ Gv(Πγ
v¨)].
This point of view may only be realized by means of a “single basepoint” of
a suitable category of coverings of a geometric object that consists of a single
connected component [cf. the discussion of Galois evaluation in Remark 1.12.4;
the discussion of [EtTh], Remark 1.10.4]. Also, we recall [cf. the discussion of
Galois evaluation in Remark 1.12.4] that this “Kummer-theoretic representation”
of the [“Frobenioid-theoretic”] monoid generated by the [“Frobenioid-theoretic”]
theta function satisfies the crucial property of being compatible [unlike the various
ring structures involved!] with the“log-wall” [cf. the theory of [AbsTopIII]].
This crucial property will play a fundamental role in the theory to be developed in
[IUTchIII].
Remark 2.6.2.
(i) In the context of the discussion of conjugate synchronization in Remark
2.6.1, it is useful to recall the theory of D-Θ±ell-Hodge theaters
†φΘ±
†HT D-Θ±ell = (†D≻
±
†φΘell
←− †DT
±
−→ †D ±)
[cf. [IUTchI], Definition 6.4, (iii)] developed in [IUTchI], §6. That is to say, from
the point of view of the theory of D-Θ±ell-Hodge theaters, it is natural to think
(a) of the topological group Πv that appears in Corollaries 2.4, 2.5, and 2.6
as the tempered fundamental group of †D≻,v,
78 SHINICHI MOCHIZUKI
(b) of the topological group Π±
v that appears in Corollaries 2.4, 2.5, and 2.6 as
the commensurator of the closure of Πv [i.e., relative to the interpretation
of (a)] inside the profinite fundamental group of †D ± relative to the
composite poly-morphism
†D≻,v
(†φΘ±
v0 )−1
−→ †Dv0
†φΘell
v0 −→ †D ±
determined by the portions of †φΘ±
± ,
†φΘell
± labeled by 0 ∈ T, v ∈ V [cf.
the discussions of [IUTchI], Examples 6.2, (i); 6.3, (i)], and
(c) of the Δ±
v -outer action of Δcor
v /Δ±
∼
→ F ±
v
l that appears in Corollary
2.4, (iii), as corresponding to the F ±
l -symmetry of [IUTchI], Proposition
6.8, (i).
Relative to the interpretation of (a), (b), and (c), one has the following fundamental
observation concerning the discussion of Remark 2.6.1:
the single basepoint that underlies the conjugate synchronization dis-
cussed in Remark 2.6.1 is compatible with the single basepoint that
underlies the label synchronization discussed in [IUTchI], Remark 6.12.4.
That is to say, both of these basepoints may be thought of as arising from a single
basepoint that gives rise to the various topological groups Πv, Π±
v , etc. that appear
in Corollaries 2.4, 2.5, and 2.6. In particular,
the conjugate synchronization discussed in Remark 2.6.1 is compat-
ible with the F ±
l -symmetry of [IUTchI], Proposition 6.8, (i) [cf. also
Remark 3.8.3 below].
Indeed, this compatibility is essentially the content of Corollary 2.4, (iii) [cf. (c)
above].
(ii) Note that the compatibility of basepoints discussed in (i) contrasts sharply
with the incompatibility of the conjugate synchronization basepoint of Remark 2.6.1
withtheFl -symmetryof[IUTchI],Proposition4.9, (i), inthecaseofD-ΘNF-Hodge
theaters. At a more concrete level, this diﬀerence between F ±
l - and Fl -symmetries
may be understood as a consequence of the fact that whereas the F ±
l -symmetry
is defined relative to a single copy of a local geometric object at v — i.e., “Π±
”
v
[cf. (a), (b), (c) above] — the Fl -symmetry involves permuting multiple copies
of local geometric objects in such a way that one may only identify these multiple
copies with one another at the expense of allowing the phenomenon of “label
crushing” [cf. the discussions of [IUTchI], Remark 4.9.2, (i), (ii); 6.12.6, (i), (ii),
(iii)].
(iii)AnotherimportantpropertyoftheF ±
l -symmetry—whichisnotsatisfied
by the Fl -symmetry! — is that the F ±
l -symmetry allows comparison with the
label zero [cf. the discussion of [IUTchI], Remark 6.12.5], hence, in particular,
comparison with the copies of “O×
k ” [cf. the discussion of Remark 1.12.2] that
occur in the splittings of Corollary 1.12, (ii), that give rise to the crucial constant
multiple rigidity of the ´ etale theta function. This important property is precisely
the content of Corollary 2.6.
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 79
Remark 2.6.3.
(i) The discussion of independent conjugacy indeterminacies in Remark 2.5.2
and of “single basepoints” that are compatible with the F ±
l -symmetry of [IUTchI],
§6, in Remarks 2.6.1, 2.6.2 imply rather severe restrictions concerning the sub-
graph “Γ¨
Y ⊆ Γ¨
Y ” of Remark 2.1.1, (ii). That is to say, suppose that one attempts
to develop the theory of the present §2 for another subgraph Γ′ of the graph Γ¨
Y.
Recall from the discussion of Remark 2.1.1, (i), that the graph Γ¨
Y may be thought
of as a “copy of the real line R”, in which the integers Z ⊆ R are taken to be the
vertices, and the line segments joining the integers are taken to be the edges. Then
the discussion of “single basepoints” [cf. Remark 2.6.1] implies, first of all, that
(a) this subgraph Γ′ must be connected.
Since, moreover, one wishes to consider the crucial splittings of Corollary 2.6, (ii)
[cf. Remark 2.6.2, (iii)], it follows that
(b) this subgraph Γ′ must contain the vertex of Γ¨
Y labeled “0”
.
The conditions (a) and (b) already impose substantial restrictions on Γ′ and hence
on the collection of values of the ´ etale theta function that may arise by restricting
to the μ−-translates of the cusps that lie in Γ′ [cf. Remark 2.5.1, (ii)] — i.e., on
the collection of
j2
q
v
obtained by allowing j ∈ Z to range [relative to the identification of the vertices of
Γ¨
Y with the integral points of the real line] over the “vertices” of Γ′ [cf. Remark
2.5.1, (i)].
(ii) By abuse of notation, let us write “j ∈ Γ′” for “vertices” j ∈ Z that lie
in Γ′. Also, for simplicity, let us assume that the subgraph Γ′ is finite [cf. (iii)
below]. Then ultimately, in the theory of [IUTchIV], when we consider various
height inequalities, we shall be concerned with the issue of maximizing the
quantity
||Γ′|| def
= |Γ′|−1
·
j∈Fl
min
j∈j Γ′
{ j2 }
— where we write |Γ′| for the cardinality of the image in Fl of the nonzero elements
of Γ′; we regard the “min” over an empty set as being equal to zero; we think of
the various j ∈ Fl as corresponding to the subsets of Z determined by the fibers
of the natural projection Z |Fl| (⊇ Fl ). Here, we observe that
(c) the set of “j’s” that occur in the “min” ranging over “j” [i.e., not over
“j”!] that appears in the definition of ||Γ′|| is always equal to a fiber
of the restriction to the set of vertices of Γ′ of the natural projection
Z |Fl|.
In fact, this observation (c) is, in essence, a consequence of the phenomenon dis-
cussed in Remark 2.5.2 of independent conjugacy indeterminacies [cf., espe-
cially, Remark 2.5.2, (iv)] — i.e., roughly speaking, that
80 SHINICHI MOCHIZUKI
one cannot restrict the ´ etale theta function to “one j ∈ Γ′” without also
restricting the ´ etale theta function to the various “other j ∈ Γ′” that lie
in the same fiber over |Fl|.
Next, let us make the [easily verified — cf. (a), (b)!] observation that if one thinks
of ||Γ′|| as a function of |Γ′|, then as |Γ′| ranges over the positive integers, it holds
that
(d) the function of |Γ′| constituted by ||Γ′|| — which may be thought of as a
sort of average — is a monotone increasing [but not strictly increasing!]
function of |Γ′| valued in the positive rational numbers which attains its
maximum when |Γ′|= l and is constant for |Γ′| ≥ l.
Now it follows formally from (d) that, as |Γ′| ranges over the positive integers, the
quantity ||Γ′|| attains its maximum when |Γ′|= l — hence, in particular, when
Γ′ is taken to be Γ¨
Y . Thus, from the point of view of the issue of maximizing this
quantity ||Γ′||, there is “no loss of generality” in assuming that Γ′ = Γ¨
Y [cf. also
the discussion of (iv) below].
(iii) Although in the discussion of (ii) above we assumed that Γ′ is finite, this
assumption does not in fact result in any loss of generality. Indeed, one verifies
immediately that ||Γ′|| is defined, finite, and satisfies the evident analogue of (d)
even for infinite Γ′. Thus, the case of infinite Γ′ may be excluded without loss of
generality.
(iv) Ultimately, in §4 of the present paper, we shall be concerned with the
issue of globalizing, via the construction of various global realified Frobenioids, the
monoids determined by the theta values at v ∈ Vbad that appear in the present §2.
This globalization will be achieved, in eﬀect, by imposing the condition that the
product formula be satisfied. On the other hand, the indeterminacies discussed
in (ii) above [cf., especially, (ii), (c)] that arise when a fiber of Γ′ over |Fl| contains
more than one element are easily seen to be fundamentally incompatible with the
product formula. In particular, from the point of view of the issue of maximiz-
ing the quantity ||Γ′||, in fact the only choice for Γ′ that is compatible with the
“globalization via the product formula” to be performed in §4 is Γ¨
Y.
(v) One may summarize the discussion of (i), (ii), (iii), and (iv) as follows:
j2
the collection of values “q
” of the ´ etale theta function determined by the
v
subgraph Γ¨
Y is of a highly distinguished nature
— and, indeed, is essentially determined [cf. the discussion at the end of (ii);
the discussion of (iv)] by the requirement of maximizing the quantity “||Γ′||” in
a fashion compatible with the global product formula, together with various
qualitative considerations that arise from Corollaries 2.4, 2.5, 2.6; the discussion of
Remarks 2.5.1, 2.5.2, 2.6.1, 2.6.2.
Definition 2.7. In the notation of Definition 2.3: Let
MΘ
∗
= {... → MΘ
M′ → MΘ
M →...}
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 81
be a projective system of mono-theta environments as in Proposition 1.5, such that
ΠX(MΘ
∗ )∼
= Πv.
(i) Write
ΠMΘ
∗
for the inverse limit of the induced projective system of topological groups {... →
ΠMΘ
→ ΠMΘ
→...} [cf. the notation discussed at the beginning of Definition
M′
M
1.1]. Thus, [in the notation of Proposition 1.5] we have a natural homomorphism
of topological groups
ΠMΘ
∗
→ ΠX(MΘ
∗ )
whose kernel may be identified with the exterior cyclotome Πμ(MΘ
∗ ), and whose
image is the subgroup of ΠX(MΘ
∗ )∼
= Πv determined by Πtp
Y
.
v
(ii) Write
ΠMΘ
∗¨
⊆ ΠMΘ
∗
⊆ ΠMΘ
∗
for the respective inverse images of Πv¨ ⊆ Πv ⊆ Πv
∼
= ΠX(MΘ
∗ ) in ΠMΘ
∗ ;
Πμ(MΘ
∗¨), (l·ΔΘ)(MΘ
∗¨), Πv¨(MΘ
∗¨), Gv(MΘ
∗¨)
for the subquotients of ΠMΘ
∗¨ determined by the subquotient Πμ(MΘ
∗ ) of ΠMΘ
and
∗
the subquotients (l·ΔΘ)(ΠX(MΘ
∗ )) [cf. Proposition 1.4], Πv¨, and Gv(ΠX(MΘ
∗ ))
[cf. Corollary 2.5, (i)] of Πv
∼
= ΠX(MΘ
∗ ). Thus, we obtain a cyclotomic rigidity
isomorphism
(l·ΔΘ)(MΘ
∗¨)∼
→ Πμ(MΘ
∗¨)
— i.e., by restricting the cyclotomic rigidity isomorphism (l·ΔΘ)(MΘ
∗ )∼
→ Πμ(MΘ
∗ )
of Proposition 1.5, (iii), to ΠMΘ
∗¨
.
Corollary 2.8. (Mono-theta-theoretic Theta Evaluation) In the notation
of Definition 2.7: Suppose that we are in the situation of Proposition 2.2, (ii);
Corollary 2.5, (ii); to simplify notation, we assume that ΠX(MΘ
∗ ) = Πv, and we
use the notation for objects constructed from “Πv” to denote the corresponding
objects constructed from ΠX(MΘ
∗ ). Also, let us write
(MΘ
∗ )γ
for the projective system of mono-theta environments obtained via transport of
∼
structure from the isomorphism Πv
→ Πγ
v determined by conjugation by γ.
´
(i) (Restriction of
Etale Theta Functions to Subgraphs and Evalu-
ation Points) In the situation of Proposition 2.2, (ii); Corollary 2.5, (ii), let us
apply the cyclotomic rigidity isomorphisms
(l·ΔΘ)((MΘ
∗¨)γ)∼
→ Πμ((MΘ
∗¨)γ); (l·ΔΘ)((MΘ
∗ )γ)∼
→ Πμ((MΘ
∗ )γ)
82 SHINICHI MOCHIZUKI
[cf. Definition 2.7, (ii), applied to (MΘ
∗ )γ] to replace“(l·ΔΘ)(−)” by “Πμ(−)”.
Then the ιγ-invariant subsets θι(Πγ
v) ⊆ θ(Πγ
v), ∞θι(Πγ
v) ⊆ ∞θ(Πγ
v) [cf. Proposition
2.2, (ii); Corollary 2.5, (ii)] determine ιγ-invariant subsets
θι
env((MΘ
∗ )γ) ⊆ θ
env((MΘ
∗ )γ);∞θι
env((MΘ
∗ )γ) ⊆ ∞θ
env((MΘ
∗ )γ)
[cf. Proposition 1.5, (iii), applied to (MΘ
∗ )γ]; restriction of these subsets θι
env((MΘ
∗ )γ),
∞θι
env((MΘ
∗ )γ) to Πv¨((MΘ
∗¨)γ) yields μ2l-, μ-orbits of elements
θι
env((MΘ
∗¨)γ) ⊆ ∞θι
env((MΘ
∗¨)γ) ⊆ lim
− →
J
H1(Πv¨((MΘ
∗¨)γ)|J,Πμ((MΘ
∗¨)γ))
— where J ⊆ Πv ranges over the open subgroups of Πv — which, upon further
restriction to the decomposition groups Dδ
t,μ− of Corollary 2.4, (ii), (c), yield
μ2l-, μ-orbits of elements
θt
env((MΘ
∗¨)γ) ⊆ ∞θt
env((MΘ
∗¨)γ) ⊆ lim
− →
JG
H1(Gv((MΘ
∗¨)γ)|JG,Πμ((MΘ
∗¨)γ))
for each t ∈ LabCusp±(Πγ
v)∼
→ LabCusp±(Πv) — where JG ⊆ Gv((MΘ
∗¨)γ) ranges
over the open subgroups of Gv((MΘ
∗¨)γ); the “∼
→ ” is induced by conjugation by γ.
Moreover, the sets θt
env((MΘ
∗¨)γ), ∞θt
env((MΘ
∗¨)γ) depend only on the label |t| ∈ |Fl|
determined by t [cf. Corollary 2.5, (ii)]. Thus, we shall write θ|t|
env((MΘ
∗¨)γ) def
=
θt
env((MΘ
∗¨)γ), ∞θ|t|
env((MΘ
∗¨)γ) def
= ∞θt
env((MΘ
∗¨)γ).
(ii) (Functorial Group-theoretic Evaluation Algorithm) If one starts
with an arbitrary Δ±
v -conjugate Πv¨((MΘ
∗¨)γ) of Πv¨(MΘ
∗¨), and one consid-
ers, as t ranges over the elements of LabCusp±(Πγ
v)∼
→ LabCusp±(Πv) [where the
“ ∼
→ ” is induced by conjugation by γ], the resulting μ2l-, μ-orbits θ|t|
env((MΘ
∗¨)γ),
∞θ|t|
env((MΘ
∗¨)γ) arising from an arbitrary Δ±
v -conjugate Iδ
t of It that is con-
tained in Πv¨((MΘ
∗¨)γ) [cf. (i)], then one obtains an algorithm for constructing
the collections of μ2l-, μ-orbits
{θ|t|
env((MΘ
∗¨)γ)}|t|∈|Fl|; {∞θ|t|
env((MΘ
∗¨)γ)}|t|∈|Fl|
which is functorial in the projective system of mono-theta environments MΘ
∗ and,
moreover, compatible with the independent conjugacy actions of Δ±
v on the
sets {Iγ1
t }γ1∈Π±
= {Iγ1
v
t }γ1∈Δ±
and {Πv¨((MΘ
v
∗¨)γ2)}γ2∈Π±
= {Πv¨((MΘ
v
∗¨)γ2)}γ2∈Δ±
v
[cf. the sets of Corollary 2.4, (i); Remark 2.2.1].
(iii) (Splittings at Zero-labeled Evaluation Points) In the situation of
(i), suppose that t is taken to be the zero element. Then, by applying the cy-
clotomic rigidity isomorphisms of (i) to replace “(l· ΔΘ)(−)” by “Πμ(−)” — an
operation that, when applied to “M??
TM(−)” [where “??” ∈ {×,μ,×μ}], we shall
denote by replacing the notation “Πγ
v¨” by “(MΘ
∗¨)γ” — in Corollary 2.6, (ii), the
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 83
second restriction operation discussed in (i) determines splittings [cf. Corollary
2.6, (ii)]
M×μ
TM ((MΘ
∗¨)γ)×{∞θι
env((MΘ
∗¨)γ)/Mμ
TM((MΘ
∗¨)γ)}
of M×
TM·
∞θι
env((MΘ
∗¨)γ)/Mμ
TM((MΘ
∗¨)γ) which are compatible, relative to the first
restriction operation discussed in (i), with the splittings of Corollary 1.12, (ii) [i.e.,
relative to any isomorphism MΘ
∼
→ MΘ
∗
∗ (Πv) — cf. Proposition 1.2, (i); Proposition
1.5, (i); Remarks 2.8.1, 2.8.2 below].
Proof. Assertions (i), (ii), and (iii) follow immediately from the definitions and
the references quoted in the statements of these assertions. ⃝
Remark 2.8.1. One may regard Corollaries 2.5, 2.6 as a special case of Corollary
2.8, i.e., thecasewheretheprojectivesystemofmono-thetaenvironmentsMΘ
∗ arises
from the topological group Πv by applying the functorial group-theoretic algorithm
of Proposition 1.2, (i) [cf. also Proposition 1.5, (i)].
Remark 2.8.2. The significance of the mono-theta-theoretic version of Corol-
laries 2.5, 2.6 constituted by Corollary 2.8 lies in the fact that this mono-theta-
theoretic version allows one to relate the group-theoretic theta evaluation theory
of the present §2 to the theory of Frobenioid-theoretic theta functions associ-
ated to tempered Frobenioids [cf. [EtTh], §5], i.e., by considering the case where
MΘ
∗ arises from a tempered Frobenioid [cf. Proposition 1.2, (ii)]. For instance, by
considering the case where MΘ
∗ arises from a tempered Frobenioid, one may treat
the Frobenioid-theoretic cyclotomes [i.e., cyclotomes that arise from the units of the
Frobenioid] of Proposition 1.3, (i), in the context of the theory of the present §2.
Remark 2.8.3.
(i) The use of the archimedean line segment ΓX ⊆ ΓX [cf. Remark 2.1.1,
(ii)] to single out the elements ∈ {−l ,−l +1,...,−1,0,1,...,l−1,l } — i.e.,
the elements with absolute value ≤ l — within the nonarchimedean congruence
classes modulo l constituted by an element ∈ Fl is reminiscent of the computation
of the set of global sections of an arithmetic line bundle on a number field [cf., e.g.,
[Szp], pp. 13-14], as well as of the arithmetic inherent in the graph theory associated
to the loop ΓX [cf. [SemiAnbd], Remark 1.5.1].
(ii) The sort of argument discussed in (i) involving the connected, “archime-
dean” line segment ΓX ⊆ ΓX [cf. Remark 2.6.1 for more on the importance of
this connectedness] depends, in an essential way, on the discreteness of Z (∼
= Z).
Put another way, this sort of argument may be thought of as an application of the
discrete rigidity that forms one of the central themes of [EtTh]. Note, moreover,
that in the context of Corollary 2.8, this application of discrete rigidity is closely
related to the application of cyclotomic rigidity. This is perhaps not so surpris-
ing, since discrete rigidity — in the form of the discreteness of squares of elements
of Z, i.e., in eﬀect, the quotient of Z by the action of {±1} — may be thought of
as a sort of dual property to the cyclotomic rigidity of “(l·ΔΘ)(−)”. Indeed, one
84 SHINICHI MOCHIZUKI
may think of this duality as being embodied in the very structure and values of the
´ etale theta function [cf. [EtTh], Proposition 1.4, (ii), (iii); [EtTh], Proposition 1.5,
(ii)].
In a similar vein, one may also consider the theory of group-theoretic theta
evaluation developed in the present §2 in the context of the natural isomorphism
“μZ(Gk)∼
→ μZ(ΠX)” of [AbsTopIII], Corollary 1.10, (c) [cf. also Proposition 1.3,
(ii); Corollary 1.11, (b)].
Corollary 2.9. (Theta Evaluation via Base-field-theoretic Cyclotomes)
Suppose that we are in the situation of Proposition 2.2, (ii); Corollary 2.5, (ii).
Also, let us write
μZ(Gv(Πv))∼
→ (l·ΔΘ)(Πv); μZ(Gv(Πγ
v¨))∼
→ (l·ΔΘ)(Πγ
v¨)
for the cyclotomic rigidity isomorphisms determined by the natural isomor-
phism “μZ(Gk)∼
→ μZ(ΠX)” of [AbsTopIII], Corollary 1.10, (c) [cf. also Propo-
sition 1.3, (ii); Corollary 1.11, (b)] and its restriction to Πγ
v¨ [cf. Corollary 2.5,
(i)].
´
(i) (Restriction of
Etale Theta Functions to Subgraphs and Eval-
uation Points) In the situation of Proposition 2.2, (ii); Corollary 2.5, (ii), let
us apply the above cyclotomic rigidity isomorphisms to replace“(l· ΔΘ)(−)” by
“μZ(Gv(−))”. Then the ιγ-invariant subsets θι(Πγ
v) ⊆ θ(Πγ
v), ∞θι(Πγ
v) ⊆ ∞θ(Πγ
v)
[cf. Proposition 2.2, (ii); Corollary 2.5, (ii)] determine ιγ-invariant subsets
θι
bs(Πγ
v) ⊆ θbs(Πγ
v);∞θι
bs(Πγ
v) ⊆ ∞θbs(Πγ
v)
— where one may think of the “bs” as an abbreviation of the term “base-field-
theoretic”; restriction of these subsets θι
bs(Πγ
v), ∞θι
bs(Πγ
v) to Πγ
v¨ yields μ2l-,
μ-orbits of elements
θι
bs(Πγ
v¨) ⊆ ∞θι
bs(Πγ
v¨) ⊆ lim
− →
J
H1(Πγ
v¨|J,μZ(Gv(Πγ
v¨)))
— where J ⊆ Πv ranges over the open subgroups of Πv — which, upon further
restriction to the decomposition groups Dδ
t,μ− of Corollary 2.4, (ii), (c), yield
μ2l-, μ-orbits of elements
θt
bs(Πγ
v¨) ⊆ ∞θt
bs(Πγ
v¨) ⊆ lim
− →
JG
H1(Gv(Πγ
v¨)|JG,μZ(Gv(Πγ
v¨)))
for each t ∈ LabCusp±(Πγ
v)∼
→ LabCusp±(Πv) — where JG ⊆ Gv(Πγ
v¨) ranges over
the open subgroups of Gv(Πγ
v¨); the “∼
→ ” is induced by conjugation by γ. Moreover,
the sets θt
bs(Πγ
v¨), ∞θt
bs(Πγ
v¨) depend only on the label |t| ∈ |Fl| determined by t
[cf. Corollary 2.5, (ii)]. Thus, we shall write θ|t|
bs(Πγ
v¨) def
= θt
bs(Πγ
v¨), ∞θ|t|
bs(Πγ
v¨) def
=
∞θt
bs(Πγ
v¨).
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 85
(ii) (Functorial Group-theoretic Evaluation Algorithm) If one starts
with an arbitrary Δ±
v -conjugate Πγ
v¨ of Πv¨, and one considers, as t ranges
over the elements of LabCusp±(Πγ
v)∼
→ LabCusp±(Πv) [where the “∼
→ ” is induced
by conjugation by γ], the resulting μ2l-, μ-orbits θ|t|
bs(Πγ
v¨), ∞θ|t|
bs(Πγ
v¨) arising from
an arbitrary Δ±
v -conjugate Iδ
t of It that is contained in Πγ
v¨ [cf. (i)], then one
obtains an algorithm for constructing the collections of μ2l-, μ-orbits
{θ|t|
bs(Πγ
v¨)}|t|∈|Fl|; {∞θ|t|
bs(Πγ
v¨)}|t|∈|Fl|
which is functorial in the topological group Πv and, moreover, compatible with
the independent conjugacy actions of Δ±
v on the sets {Iγ1
t }γ1∈Π±
= {Iγ1
v
t }γ1∈Δ±
v
and {Πγ2
v¨}γ2∈Π±
= {Πγ2
v
v¨}γ2∈Δ±
[cf. the sets of Corollary 2.4, (i); Remark 2.2.1].
v
(iii) (Splittings at Zero-labeled Evaluation Points) In the situation of
(i), suppose that t is taken to be the zero element. Then, by applying the cyclo-
tomic rigidity isomorphisms reviewed above to replace “(l·ΔΘ)(−)” by “μZ(Gv(−))”
— an operation that, when applied to “M??
TM(−)” [where “??” ∈ {×,μ,×μ}], we
shall denote by means of a subscript “bs” — in Corollary 2.6, (ii), the second
restriction operation discussed in (i) determines splittings [cf. Corollary 2.6, (ii)]
M×μ
TM (Πγ
v¨)bs ×{∞θι
bs(Πγ
v¨)/Mμ
TM(Πγ
v¨)bs}
of M×
TM·
∞θι
bs(Πγ
v¨)/Mμ
TM(Πγ
v¨)bs which are compatible, relative to the first re-
striction operation discussed in (i) and the cyclotomic rigidity isomorphisms re-
viewed above, with the splittings of Corollary 1.12, (ii).
Proof. Assertions (i), (ii), and (iii) follow immediately from the definitions and
the references quoted in the statements of these assertions. ⃝
Remark 2.9.1.
(i) Let us recall that [the cyclotomic rigidity isomorphisms involving] the cyclo-
tomes “Πμ(−)” that appear in Corollary 2.8 admit a multiradial formulation [cf.
Corollary 1.10]. By contrast, at least relative to the point of view of Remark 1.11.3,
(iv), [the cyclotomic rigidity isomorphisms involving] the cyclotomes “μZ(Gv(−))”
that appear in Corollary 2.9 only admit a uniradial formulation — i.e., unless one
is willing to sacrifice the crucial cyclotomic rigidity under consideration as in the
formulation of Corollary 1.11.
(ii) On the other hand, the use of [the cyclotomic rigidity isomorphisms involv-
ing] the cyclotomes “μZ(Gv(−))” has the crucial advantage that it allows one to
apply the [not multiradially (!), but rather] uniradially defined natural surjection
H1(Gv(−),μZ(Gv(−))) Z
of Remark 1.11.5, (i), (ii).
86 SHINICHI MOCHIZUKI
(iii) One immediate consequence of the discussion of (i) is the observation
that, at least relative to the point of view of Remark 1.11.3, (iv), the algorithms of
Corollary 2.9, (ii), (iii), only give rise to a uniradially defined functor. On the
other hand, one important consequence of the theory to be developed in [IUTchIII]
is the result that,
by applying the theory of log-shells [cf. [AbsTopIII]], one may modify
these algorithms in such a way as to obtain algorithms that [yield functors
which] are manifestly multiradially defined
— albeit at the cost of allowing for certain [relatively mild!] indeterminacies.
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 87
Section 3: Tempered Gaussian Frobenioids
In the present §3, we relate the theory of group-theoretic algorithms surround-
ing the Hodge-Arakelov-theoretic evaluation of the ´ etale theta function on
l-torsion points developed in §1, §2 to the local portion at bad primes [i.e., at
v ∈ Vbad] of the various Frobenioids considered in [IUTchI], §3, §4, §5, §6. In par-
ticular, we shall discuss how the various multiradial formulations developed in §1
and the theory of conjugate synchronization developed in §2 may be applied
in the context of the “tempered Gaussian Frobenioids” that arise from the
Hodge-Arakelov-theoretic evaluation of the ´ etale theta function on l-torsion points.
In the present §3, we shall continue to use the notation of §2. In particular,
our discussion concerns the local portion at v ∈ Vbad of the various mathematical
objects considered in [IUTchI], §3, §4, §5, §6.
Proposition 3.1. (Mono-theta-theoretic Theta Monoids) Let
MΘ
∗
= {... → MΘ
M′ → MΘ
M →...}
be a projective system of mono-theta environments [cf. Proposition 1.5,
Corollary 2.8] such that ΠX(MΘ
∗ )∼
= Πv. In the following, to simplify the notation,
we shall denote a “ΠX(MΘ
∗ )” in parenthesis by means of the abbreviated notation
“MΘ
∗ ”.
(i) (Split Theta Monoids) By applying the constructions of Proposition
1.5, (iii); Corollary 2.8, (i) [cf. also Corollary 1.12, (d)], one obtains a functorial
algorithm
MΘ
∗ → M×
TM(MΘ
∗ ), θι
env(MΘ
∗ ), ∞θι
env(MΘ
∗ ),
M×
TM·
∞θι
env(MΘ
∗ ) ⊆ lim
− →
J
H1(Π¨
Y (MΘ
∗ )|J,Πμ(MΘ
∗ ))
ι
— where J ranges over the finite index open subgroups of ΠX(MΘ
∗ ), and ι ranges
over the inversion automorphisms of Proposition 2.2, (i) — for constructing var-
ious subsets of the direct limit of cohomology modules in the above display; this
collection of subsets is equipped with a natural conjugation action by ΠX(MΘ
∗ ).
In particular, one obtains a functorial algorithm for constructing the data
Ψenv(MΘ
∗ ) def
= Ψι
env(MΘ
∗ ) = M×
TM(MΘ
∗ )·θι
env(MΘ
∗ )N
;
ι
∞Ψenv(MΘ
∗ ) def
= ∞Ψι
env(MΘ
∗ ) = M×
TM(MΘ
∗ )·
∞θι
env(MΘ
∗ )N
ι
consisting of the submonoids {Ψι
env(MΘ
∗ )}ι, {∞Ψι
env(MΘ
∗ )}ι [of the direct limit of
cohomology modules in the first display of the present (i)] generated, respectively,
by the subsets “M×
TM· θι
env(MΘ
∗ )”, “M×
TM·
∞θι
env(MΘ
∗ )”, as well as a functorial
algorithm for constructing the splittings up to torsion determined by the subsets
“M×
TM(MΘ
∗ )”, “θι
env(MΘ
∗ )”, “∞θι
env(MΘ
∗ )” [cf. Corollary 2.8, (iii)]. We shall refer
to each Ψι
env(MΘ
∗ ), ∞Ψι
env(MΘ
∗ ) as a theta monoid.
88 SHINICHI MOCHIZUKI
(ii) (Constant Monoids) By applying the cyclotomic rigidity isomor-
phisms of Corollaries 2.8, (i); 2.9, and considering the inverse image of Z ⊆ Z
via the surjection of Remark 1.11.5, (i), applied to Gv(MΘ
∗ ) (= Gv(ΠX(MΘ
∗ ))) [cf.
the notation of Corollary 2.5, (i)], one obtains a functorial algorithm
MΘ
∗ → Ψcns(MΘ
∗ ) def
= MTM(MΘ
∗ ) ⊆ lim
− →
J
H1(Π¨
Y (MΘ
∗ )|J,Πμ(MΘ
∗ ))
[where J is as in (i)] for constructing a “monoid of constants” — i.e., which is
naturally isomorphic to O◃
[cf. Example 1.8, (ii)] — equipped with a natural
Fv
conjugation action by ΠX(MΘ
∗ ). We shall refer to Ψcns(MΘ
∗ ) as a constant
monoid.
Proof. Assertions (i) and (ii) follow immediately from the definitions and the
references quoted in the statements of these assertions. ⃝
Before proceeding, we pause to review the theory of tempered Frobenioids dis-
cussed in [IUTchI], Example 3.2.
Example 3.2. Theta Monoids Constructed from Tempered Frobenioids.
In the situation of [IUTchI], Example 3.2:
(i) Recall the tempered Frobenioid F
v of [IUTchI], Example 3.2, (i), (ii), (v)
[cf. also [IUTchI], Remark 3.2.3, (i), (ii)]. Then, in the notation of loc. cit., the
choice of a Frobenioid-theoretic theta function
Θ
v
∈ O×(T÷
¨
Y
)
v
— i.e., among the μ2l(T÷
¨
Y
¨
)-multiples of the AutDv(
Y
v)-conjugates of Θ
— deter-
v
v
mines a monoid O◃
CΘ
(−) on DΘ
v . Now suppose, for simplicity, that the topological
v
group Πv arises from a basepoint, i.e., more concretely, from a “universal covering
pro-object” AΘ
∞ of Dv [i.e., a pro-object determined by a cofinal projective system
of Galois objects of Dv]. Then by evaluating O◃
CΘ
(−) on [the “universal covering
v
pro-object” of DΘ
v determined by] AΘ
∞, we obtain submonoids [in the usual sense]
def
= O◃
CΘ
v
(AΘ
∞) = O×
CΘ
v
(AΘ
∞)·ΘN
v|AΘ
∞
⊆ ∞ΨFΘ
v ,id
def
= O×
CΘ
v
(AΘ
∞)·ΘQ≥0
v |AΘ
∞
⊆ O×(T÷
AΘ
∞
)
— where the superscript “Q≥0” denotes the set of elements for which some [positive
integer] power is equal to a [positive integer] power of Θv|AΘ
∞. In a similar vein,
by considering [cf. [IUTchI], Remark 3.2.3, (i)] the various conjugates Θα
of Θ
v
v,
¨
for α ∈ AutDv(
Y
v), we also obtain submonoids ΨFΘ
v ,α ⊆ ∞ΨFΘ
v ,α ⊆ O×(T÷
AΘ
∞
ΨFΘ
v ,id
).
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 89
¨
Moreover, one has a natural surjection Πv AutDv(
Y
v), as well as a natural
conjugation action of Πv on the collections of submonoids
ΨFΘ
v
def
= ΨFΘ
v ,α
; ∞ΨFΘ
α∈Πv
v
def
= ∞ΨFΘ
v ,α
α∈Πv
— i.e., where, by abuse of notation, we think of the subscripted “α’s” as denoting
¨
the image of “α” via the surjection Πv AutDv(
Y
v). Also, we recall from loc. cit.
that ΘQ≥0
v |AΘ
determines characteristic splittings, up to torsion, of the monoids
∞
ΨFΘ
v ,α [cf. the “τΘ
v ” of [IUTchI], Example 3.2, (v)],∞ΨFΘ
v ,α which are compatible
with the action of Πv. Finally, we recall that the collection of data
Πv ΨFΘ
v
= ΨFΘ
v ,α
, ∞ΨFΘ
α∈Πv
v
= ∞ΨFΘ
v ,α
α∈Πv
— i.e., consisting of two collections of submonoids of the group of units [namely,
O×(T÷
AΘ
)] associated to the birationalization of a certain characteristic pro-object
∞
of F
v, equipped with the conjugation action by an automorphism group of a certain
characteristic pro-object of Dv — as well as the characteristic splittings, up to
torsion, just discussed, may be reconstructed category-theoretically from F
v
[cf. [IUTchI], Example 3.2, (vi), (e)], up to an indeterminacy arising from the inner
automorphisms of Πv.
(ii) In a similar, but somewhat simpler, vein, the Frobenioid structure on
the subcategory Cv ⊆ F
v — i.e., the “base-field-theoretic hull” of the tempered
Frobenioid F
v [cf. [IUTchI], Example 3.2, (iii)] — determines, via the general
theory of Frobenioids [cf. [FrdI], Proposition 2.2], a monoid O◃
Cv(−) on Dv. Then
by evaluating O◃
Cv(−) on AΘ
∞, we obtain a monoid [in the usual sense]
ΨCv
def
= O◃
Cv(AΘ
∞)
whichisequippedwithanatural actionbyΠv. Finally,werecallthatthecollection
Πv ΨCv
— i.e., consisting of a submonoid of the group of units [namely, O×(T÷
AΘ
)] associ-
∞
ated to the birationalization of a certain characteristic pro-object of F
v, equipped
with the conjugation action by an automorphism group of a certain characteristic
pro-object of Dv — may be reconstructed category-theoretically from F
v [cf.
[IUTchI], Example 3.2, (iii); [IUTchI], Example 3.2, (vi), (d); [FrdI], Theorem 3.4,
(iv); [FrdII], Theorem 1.2, (i); [FrdII], Example 1.3, (i)], up to an indeterminacy
arising from the inner automorphisms of Πv.
Proposition 3.3. (Frobenioid-theoretic Theta Monoids) Suppose, in the
situation of Proposition 3.1, that MΘ
∗ arises [cf. Proposition 1.2, (ii)] from a tem-
pered Frobenioid †F
v — i.e.,
MΘ
∗
of data
= MΘ
∗ (†F
v)
= ∞Ψ†FΘ
v ,α
α∈ΠX(MΘ
∗ );
90 SHINICHI MOCHIZUKI
— that appears in a Θ-Hodge theater †HT Θ = ({†F
w}w∈V,
†Fmod) [cf. [IUTchI],
Definition 3.6] — cf., for instance, the Frobenioid “F
v” of [IUTchI], Example 3.2,
(i). Observe that by applying the category-theoretic constructions of Example 3.2,
(i), (ii), to †F
v, one obtains data
ΠX(MΘ
∗ ) Ψ†FΘ
v
= Ψ†FΘ
v ,α
α∈ΠX(MΘ
∗ ), ∞Ψ†FΘ
v
ΠX(MΘ
∗ ) Ψ†Cv
as well as splittings, up to torsion, of each of the monoids Ψ†FΘ
v ,α, ∞Ψ†FΘ
v ,α.
(i) (Split Theta Monoids) By forming Kummer classes relative to the
Frobenioid structure of †F
v — i.e., in essence, by considering the Galois coho-
mology classes that arise when one extracts N-th roots of unity for N ∈ N≥1 [cf.
[FrdII], Definition 2.1, (ii); [IUTchI], Remark 3.2.3, (ii); the discussion of [EtTh],
§5] — and applying the description given in Proposition 1.3, (i), of the exterior
cyclotome of a mono-theta environment that arises from a tempered Frobenioid,
¨
one obtains, for a suitable bijection of l·Z-torsors between [Gal(
Y
v/Yv)-orbits
of] “ι” as in Proposition 2.2, (i), and images of “α” via the natural surjection
Πv l·Z, collections of isomorphisms of monoids
Ψ†FΘ
v ,α
∼
→ Ψι
env(MΘ
∗ );∞Ψ†FΘ
v ,α
∼
→ ∞Ψι
env(MΘ
∗ )
— each of which is well-defined up to composition with an inner automorphism
[cf. the discussion of Example 3.2, (i)] and compatible with both the respective
conjugation actions by ΠX(MΘ
∗ ) and the splittings up to torsion on the monoids
under consideration. We shall denote these collections of isomorphisms by means
of the notation
Ψ†FΘ
v
∼
→ Ψenv(MΘ
∗ );∞Ψ†FΘ
v
∼
→ ∞Ψenv(MΘ
∗ )
[cf. the notation of Proposition 3.1, (i); Example 3.2, (i)].
(ii) (Constant Monoids) By forming Kummer classes relative to the Frobe-
nioid structure of †F
v — i.e., in essence, by considering the Galois cohomology
classes that arise when one extracts N-th roots of unity for N ∈ N≥1 [cf. [FrdII],
Definition 2.1, (ii); [IUTchI], Remark 3.2.3, (ii); [FrdII], Theorem 2.4] — and ap-
plying the description given in Proposition 1.3, (i), of the exterior cyclotome of
a mono-theta environment that arises from a tempered Frobenioid, one obtains an
isomorphism of monoids
Ψ†Cv
∼
→ Ψcns(MΘ
∗ )
— which is well-defined up to composition with an inner automorphism [cf. the
discussion of Example 3.2, (ii)] and compatible with the respective conjugation
actions by ΠX(MΘ
∗ ).
Proof. Assertions (i) and (ii) follow immediately from the definitions and the
references quoted in the statements of these assertions. ⃝
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 91
Proposition 3.4. (Group-theoretic Theta Monoids) Let †F
be a tem-
v
pered Frobenioid as in Proposition 3.3. Consider the full poly-isomorphism
MΘ
∗ (Πv)∼
→ MΘ
∗ (†F
v)
— where MΘ
∗ (Πv) is the projective system of mono-theta environments arising from
the algorithm of Proposition 1.2, (i) [cf. also Proposition 1.5, (i)] — of projective
systems of mono-theta environments.
(i) (Multiradiality of Split Theta Monoids) Each isomorphism of projec-
tive systems of mono-theta environments MΘ
∗ (Πv)∼
→ MΘ
∗ (†F
v) induces compati-
ble [in the evident sense] collections of isomorphisms
∼
Πv
→ ΠX(MΘ
∗ (Πv))∼
→ ΠX(MΘ
∗ (†F
v)) = ΠX(MΘ
∗ (†F
v))
∞Ψenv(MΘ
∗ (Πv))∼
→ ∞Ψenv(MΘ
∗ (†F
v))∼
→ ∞Ψ†FΘ
v ;
Ψenv(MΘ
∗ (Πv))∼
→ Ψenv(MΘ
∗ (†F
v))∼
→ Ψ†FΘ
v
and
Gv
∼
→ Gv(MΘ
∗ (Πv))∼
→ Gv(MΘ
∗ (†F
v)) = Gv(MΘ
∗ (†F
v))
Ψenv(MΘ
∗ (Πv))× ∼
→ Ψenv(MΘ
∗ (†F
v))× ∼
→ (Ψ†FΘ
v )×
— where the upper horizontal isomorphisms in each diagram are isomorphisms
of topological groups; the lower/middle horizontal isomorphisms in each diagram
are isomorphisms of [ind-topological] monoids; the lower/middle horizontal iso-
morphisms in the first diagram are compatible with the respective splittings up to
torsion; the left-hand square in each diagram arises from the functoriality of the
algorithms involved, relative to isomorphisms of projective systems of mono-theta
environments; the right-hand square in each diagram arises from the inverses of
the isomorphisms of the second display of Proposition 3.3, (i); the superscript “×”
denotes the submonoid of units; the notation “Gv(−)” is as in Proposition 3.1, (ii).
Finally, if we write (Ψ†FΘ
v )×μ for the ind-topological monoid obtained by forming
the quotient of (Ψ†FΘ
v )× by its torsion subgroup, then the functorial algorithms
Πv → Ψenv(MΘ
∗ (Πv)); Πv → ∞Ψenv(MΘ
∗ (Πv))
— where we think of Ψenv(MΘ
∗ (Πv)), ∞Ψenv(MΘ
∗ (Πv)) as being equipped with their
natural Πv-actions and splittings up to torsion [cf. Proposition 3.1, (i)] — obtained
by composing the algorithms of Propositions 1.2, (i); 3.1, (i), are compatible,
relative to the above displayed diagrams, with arbitrary automorphisms of [the
underlying pair, consisting of an ind-topological monoid equipped with the action of
a topological group, determined by] the pair
Gv(MΘ
∗ (†F
v)) (Ψ†FΘ
v )×μ
92 SHINICHI MOCHIZUKI
which arise as Ism-multiples of automorphisms induced by automorphisms of [the
underlying pair, consisting of an ind-topological monoid equipped with the action
of a topological group, determined by] the pair Gv(MΘ
∗ (†F
v)) (Ψ†FΘ
v )× [cf.
Example 1.8, (iv); Remark 1.8.1; Remark 1.11.1, (i), (b)] — in the sense that the
natural functor “ΨR” of Corollary 1.12, (iii), is multiradially defined.
(ii) (Uniradiality of Constant Monoids) Each isomorphism of projective
systems of mono-theta environments MΘ
∗ (Πv)∼
→ MΘ
∗ (†F
v) induces compatible
collections of isomorphisms
Πv
∼
→ ΠX(MΘ
∗ (Πv))∼
→ ΠX(MΘ
∗ (†F
v)) = ΠX(MΘ
∗ (†F
v))
Ψcns(MΘ
∗ (Πv))∼
→ Ψcns(MΘ
∗ (†F
v))∼
→ Ψ†Cv
and
Gv
∼
→ Gv(MΘ
∗ (Πv))∼
→ Gv(MΘ
∗ (†F
v)) = Gv(MΘ
∗ (†F
v))
Ψcns(MΘ
∗ (Πv))× ∼
→ Ψcns(MΘ
∗ (†F
v))× ∼
→ (Ψ†Cv)×
— where the upper horizontal isomorphisms in each diagram are isomorphisms of
topological groups; the lower horizontal isomorphisms in each diagram are isomor-
phisms of [ind-topological] monoids; the second diagram may be naturally iden-
tified with the second displayed commutative diagram of (i); the left-hand square
in each diagram arises from the functoriality of the algorithms involved, relative
to isomorphisms of projective systems of mono-theta environments; the right-hand
square in each diagram arises from the inverse of the displayed isomorphism of
Proposition 3.3, (ii); the superscript “×” denotes the submonoid of units; the no-
tation “Gv(−)” is as in Proposition 3.1, (ii). Finally, if we write (Ψ†Cv)×μ for the
ind-topological monoid obtained by forming the quotient of (Ψ†Cv)× by its torsion
subgroup, then the functorial algorithm
Πv → Ψcns(MΘ
∗ (Πv))
— where we think of Ψcns(MΘ
∗ (Πv)) as being equipped with its natural Πv-action
[cf. Proposition 3.1, (ii)] — obtained by composing the algorithms of Proposition
1.2, (i); 3.1, (ii), depends on the cyclotomic rigidity isomorphism of Corollary
1.11, (b) [cf. Remark 1.11.5, (ii); the use of the surjection of Remark 1.11.5, (i),
in the algorithm of Proposition 3.1, (ii)], hence fails to be compatible, relative
to the above displayed diagrams, with automorphisms of [the underlying pair,
consisting of an ind-topological monoid equipped with the action of a topological
group, determined by] the pair
Gv(MΘ
∗ (†F
v)) (Ψ†Cv)×μ
which arise from automorphisms of [the underlying pair, consisting of an ind-
topological monoid equipped with the action of a topological group, determined by]
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 93
the pair Gv(MΘ
∗ (†F
v)) (Ψ†Cv)× [cf. Remarks 1.11.1, (i), (b); 1.8.1] — in
the sense that this algorithm, as given, only admits a uniradial formulation [cf.
Remarks 1.11.3, (iv); 1.11.5, (ii)].
Proof. Assertions (i) and (ii) follow immediately from the definitions and the
references quoted in the statements of these assertions. ⃝
Remark 3.4.1.
(i) Note that the pairs
“Gv(MΘ
∗ (†F
v)) (Ψ†FΘ
v )×μ” and “Gv(MΘ
∗ (†F
v)) (Ψ†Cv)×μ”
that appear in Proposition 3.4, (i), (ii), correspond to the pair “G O×μ(G)”
that appears in the discussion of Remark 1.11.3, (ii) — i.e., the data that arises by
replacing the “O×” that appears in the Θ-link of [IUTchI], Corollary 3.7, (iii), by
“O×μ”. That is to say, from the point of view of the present series of papers, the
significance of Proposition 3.4 lies in the point of view that
the multiradiality (respectively, uniradiality) asserted in Proposition
3.4, (i) (respectively, (ii)), may be thought of as a statement of the com-
patibility (respectively, incompatibility) of the algorithm in question
with the “O×μ-version” of the Θ-link of [IUTchI], Corollary 3.7, (iii).
(ii) One important consequence of the theory to be developed in [IUTchIII] [cf.
Remark 2.9.1, (iii)] is the result that,
by applying the theory of log-shells [cf. [AbsTopIII]], one may construct
certain algorithms related to the algorithm of Proposition 3.4, (ii), that
[yield functors which] are manifestly multiradially defined
— albeit at the cost of allowing for certain [relatively mild!] indeterminacies.
The following two corollaries will play a fundamental role in the present series
of papers.
Corollary 3.5. (Mono-theta-theoretic Gaussian Monoids) Let MΘ
∗ be as
in Proposition 3.1 [cf. also Corollary 2.8, in the case where γ = 1; Remark 3.5.1
below]. For t ∈ LabCusp±(ΠX(MΘ
∗ )), we shall denote copies labeled by t of various
objects functorially constructed from MΘ
∗ by means of a subscript“t”. Also, we
shall write
ΠX(MΘ
∗ ) ⊆ ΠX(MΘ
∗ ) ⊆ ΠC(MΘ
∗ )
ΔX(MΘ
∗ ) ⊆ ΔX(MΘ
∗ ) ⊆ ΔC(MΘ
∗ )
for the inclusions — which may be functorially constructed from ΠX(MΘ
∗ ) — cor-
responding to the inclusions Πv ⊆ Π±
v ⊆ Πcor
v , Δv ⊆ Δ±
v ⊆ Δcor
v of Definition 2.3,
(i).
94 SHINICHI MOCHIZUKI
(i) (Labels, F ±
l -Symmetries, and Conjugate Synchronization) If we
think of the cuspidal inertia groups ⊆ ΠX(MΘ
∗ ) corresponding to t as subgroups
of cuspidal inertia groups of ΠX(MΘ
∗ ) [cf. Remark 2.3.1], then the ΔX(MΘ
∗ )-outer
action of F ±
∼
l
= ΔC(MΘ
∗ )/ΔX(MΘ
∗ ) on ΠX(MΘ
∗ ) [cf. Corollary 2.4, (iii); Remark
1.1.1, (iv), or, alternatively, when applicable, Proposition 1.3, (ii), (iii)] induces
isomorphisms between the pairs
Gv(MΘ
∗¨)t Ψcns(MΘ
∗ )t
— consisting of a labeled ind-topological monoid equipped with the action of a
labeled topological group [cf. Proposition 3.1, (ii)] — for distinct t ∈ LabCusp±
(ΠX(MΘ
∗ )). We shall refer to these isomorphisms as [F ±
l -]symmetrizing iso-
morphisms [cf. Remark 3.5.2 below]. We shall denote by means of a subscript
“|t| ∈ |Fl|” the result of identifying copies labeled by t,−t via a suitable sym-
metrizing isomorphism. We shall denote by means of a subscript “⟨|Fl|⟩” (respec-
tively, “⟨Fl ⟩”) the diagonal embedding, determined by suitable symmetrizing
isomorphisms, inside the direct product of copies labeled by |t| ∈ |Fl| (respectively,
|t| ∈ Fl ). In particular, by restricting the monoid Ψcns(MΘ
∗ ) of Proposition 3.1,
(ii), via the restriction operations [i.e., to “ΠMΘ
” and “Dδ
∗¨
t,μ−”] described in detail
in Corollary 2.8, (i), (ii), one obtains a collection of compatible morphisms
ΠX(MΘ
∗ ) ← Πv¨(MΘ
∗¨) Gv(MΘ
∗¨)⟨|Fl|⟩
Ψcns(MΘ
∗ )∼
→ Ψcns(MΘ
∗ )⟨|Fl|⟩
— where the notation “ ” denotes the natural actions; the bottom horizontal arrow
is an isomorphism of monoids — which are compatible with the various sym-
metrizing isomorphisms and well-defined up to composition with an inner
automorphism of ΠX(MΘ
∗ ) [i.e., up to composition with the conjugation action
by ΠX(MΘ
∗ ) on the pair Πv¨(MΘ
∗¨) Ψcns(MΘ
∗ )]. Put another way, this inner
automorphism indeterminacy — which, a priori, depends on the index |t| — is, in
fact, independent of |t| ∈ |Fl|.
(ii) (Gaussian Monoids) We shall refer to an element of the set
θFl
env(MΘ
∗¨) def
=
θ|t|
env(MΘ
∗¨) ⊆
Ψcns(MΘ
∗ )|t|
|t|∈Fl
|t|∈Fl
[cf. the notation of Corollary 2.8, (i), (ii)] — which is of cardinality (2l)l
—
as a value-profile. Then by applying [the various objects constructed from] the
symmetrizing isomorphisms of (i), together with the functorial algorithm [for
restricting elements of θι
env(MΘ
∗ ), ∞θι
env(MΘ
∗ )] of Corollary 2.8, (i), (ii), one obtains
a functorial algorithm for constructing two collections of submonoids
MΘ
∗ →
Ψgau(MΘ
∗ ) def
= Ψξ(MΘ
∗ ) def = Ψ×
cns(MΘ
∗ )⟨Fl ⟩·ξN ⊆
Ψcns(MΘ
∗ )|t| ξ
,
|t|∈Fl
∞Ψgau(MΘ
∗ ) def
= ∞Ψξ(MΘ
∗ ) def = Ψ×
cns(MΘ
∗ )⟨Fl ⟩·ξQ≥0 ⊆
Ψcns(MΘ
∗ )|t| ξ|t|∈Fl
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 95
— where the superscript “×” denotes the submonoid of units; ξ ranges over the
value-profiles; “ξQ≥0” denotes the submonoid generated by the N-th roots [for
N ∈ N≥1] of ξ [which are uniquely determined, up to multiplication by an ele-
ment of the N-torsion subgroup of Ψ×
cns(MΘ
∗ )⟨Fl ⟩!] that arise by restricting elements
of∞θι
env(MΘ
∗ ); each Ψξ(MΘ
∗ ) is equipped with a natural action by Gv(MΘ
∗¨)⟨Fl ⟩.
We shall refer to each Ψξ(MΘ
∗ ) or ∞Ψξ(MΘ
∗ ) as a Gaussian monoid. Here, the
submonoid Ψ2l·ξ(MΘ
∗ ) ⊆ Ψξ(MΘ
∗ ) generated by Ψ×
cns(MΘ
∗ )⟨Fl ⟩ and ξ2l·N is indepen-
dent of the value-profile ξ. Finally, the restriction operations described in detail
in Corollary 2.8, (i), (ii), determine a collection of compatible [in the evident
sense] morphisms [cf. Remark 3.6.1 below]
ΠX(MΘ
∗ ) ← Πv¨(MΘ
∗¨) {Gv(MΘ
∗¨)|t|}|t|∈Fl
∞Ψι
env(MΘ
∗ )∼
→ ∞Ψξ(MΘ
∗ )
Ψι
env(MΘ
∗ )∼
→ Ψξ(MΘ
∗ )
— where the “ ” in the first line denotes the compatibility of the action [de-
noted by the second “ ” in the second line] of Gv(MΘ
∗¨)|t| on the factor labeled
“|t|” of the direct product containing∞Ψξ(MΘ
∗ ) [cf. the definition of∞Ψξ(MΘ
∗ )]
with the inclusions Gv(MΘ
∗ ) → Πv¨(MΘ
∗¨) determined by the various choices of
the “Dδ
t,μ−” [cf. Corollary 2.8, (i), (ii)] that gave rise to the value-profile ξ; the
first “ ” in the second line denotes the natural action; the lower/middle horizontal
arrows are isomorphisms of monoids — which is well-defined up to composition
with a(n) [single!] inner automorphism of ΠX(MΘ
∗ ) and compatible [in the ev-
ident sense] with the equalities of submonoids Ψ2l·ξ1(MΘ
∗ ) = Ψ2l·ξ2(MΘ
∗ ) for distinct
value-profiles ξ1, ξ2. For simplicity, we shall use the notation
Ψenv(MΘ
∗ )∼
→ Ψgau(MΘ
∗ );∞Ψenv(MΘ
∗ )∼
→ ∞Ψgau(MΘ
∗ )
to denote these collections of compatible morphisms induced by restriction.
(iii) (Constant Monoids and Splittings) Denote the zero element of |Fl|
by 0 ∈ |Fl|. Then [in the notation of (i)] the diagonal submonoid Ψcns(MΘ
∗ )⟨|Fl|⟩
determines — i.e., may be thought of as the graph of — an isomorphism of
monoids
Ψcns(MΘ
∗ )0
∼
→ Ψcns(MΘ
∗ )⟨Fl ⟩
that is compatible with the respective labeled Gv(MΘ
∗¨)-actions. Moreover, the
restriction operations to zero-labeled evaluation points described in detail in
Corollary 2.8, (i), (ii), (iii), determine a splitting up to torsion of each of the
Gaussian monoids
Ψξ(MΘ
∗ ) = Ψ×
cns(MΘ
∗ )⟨Fl ⟩· ξN
, ∞Ψξ(MΘ
∗ ) = Ψ×
cns(MΘ
∗ )⟨Fl ⟩· ξQ≥0
[cf. the definition of Ψξ(MΘ
∗ ), ∞Ψξ(MΘ
∗ ) in (ii)] which is compatible, relative to
the restriction isomorphisms of the third display of (ii), with the splittings up
to torsion of Proposition 3.1, (i).
96 SHINICHI MOCHIZUKI
Proof. The various assertions of Corollary 3.5 follow immediately from the defini-
tions and the references quoted in the statements of these assertions. ⃝
Remark 3.5.1.
(i) Note that in Corollary 3.5, unlike the situation of Corollary 2.8, we took γ
to be = 1. This was done primarily to simplify the notation and does not result in
any substantive loss of generality. Indeed, one may always simply take the “MΘ
∗ ” of
Corollary 3.5 to be the “(MΘ
∗ )γ” of Corollary 2.8. Alternatively, one may observe
that the “δ” that appears in the “Dδ
” that occurs in the various restriction
t,μ−
operations invoked in Corollary 3.5 [cf. Corollary 2.8, (i), (ii)] is arbitrary, i.e., it is
subject to the independent conjugation indeterminacies discussed in Corollary 2.5,
(iii); Remark 2.5.2.
(ii) In the present context, it is useful to recall that from the point of view
of the discussion of [IUTchI], Remark 3.2.3, (i), the various ΠX(MΘ
∗ )-conjugacy
indeterminacies that appear in Corollary 3.5 are applied, in the context of the
theory of the present series of papers, to identify the various ΠX(MΘ
∗ )-conjugates
of Πv¨(MΘ
∗¨) [or, alternatively, “ι’s”] with one another.
Remark 3.5.2. Beforeproceeding, itisusefultopausetoconsiderthesignificance
of the symmetrizing isomorphisms of Corollary 3.5, (i).
(i) We begin by discussing a simple combinatorial model of the phenomenon
of interest. Consider the totally ordered set E= {0,1} whose ordering is completely
determined by the inequality
0 < 1
— which we shall denote, in the following discussion, by the notation “≺”. Then
one may consider labeled copies
≺0, ≺1
of ≺. Now suppose that one attempts to identify these labeled copies ≺0, ≺1 by
simply forgetting the labels. This amounts, in eﬀect, to sending the two distinct
subscripted labels
E ∋ 0, 1 → ∗
to a single point“∗”. In particular, this naive approach to identifying the labeled
copies ≺0, ≺1 fails to be compatible — in a sense that we shall examine in more
detail in the discussion to follow — with operations that require one to distinguish
the two labels 0,1 ∈ E. Now if, to avoid confusion, one writes S for the underlying
set of E [i.e., obtained from E by forgetting the ordering on E], then one has a
natural Aut(S)-orbit of bijections
E∼
→ S Aut(S)
— where Aut(S)∼
= Z/2Z. Next, let us suppose that we are given an object F(≺)
functorially constructed from [the “totally ordered set of cardinality two”] ≺. Then
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 97
any “factorization” of the functorial construction F(−) [i.e., on “totally ordered
sets of cardinality two”] through a functorial construction
Fsym(S) Aut(S)
on unordered sets of cardinality two [i.e., relative to the “forgetful functor” that
associates to an ordered set the underlying unordered set] may be thought of as
a collection of “symmetrizing isomorphisms” [cf. the discussion of (ii) below;
Corollary 3.5, (i)], or, alternatively, as “descent data” for F(−) from E to the
“orbiset quotient” of S by Aut(S). Moreover, this “descent data” satisfies the
crucial property that it allows one to perform this “descent to the orbiset quotient”
in such a way that one is
never required to violate the bijective relationship — albeit via an in-
determinate bijection! — between E and S.
By contrast, the “naive approach” discussed above may be thought of as corre-
sponding to working with the “coarse set-theoretic quotient” Q of S by Aut(S)
def
— which we shall think of as consisting of a single point ∗
= {0,1} ∈ Q= {∗}.
Now suppose, for instance, in the case F(≺) def
=≺, that one attempts to regard
def
F(≺)(−)
=≺(−) [where (−) ∈ S] as an object “pulled back” from a copy ≺Q [i.e.,
“0Q < 1Q”] of ≺ over Q. On the other hand, if one wishes to relate each point
def
s ∈ S to one or more points ∈ EQ
= {0Q,1Q} via an Aut(S)-equivariant assign-
ment in such a way that every point of EQ appears in the image of this assignment,
then one has no choice but to assign to each point s ∈ S the collection of all points
∈ EQ. Put another way, one must contend with an independent indeterminacy
s → 0Q? 1Q?
for each s ∈ S — i.e., if we write S= {0S,1S}, then these indeterminacies give rise
to a total of 4 possibilities
0S → 0Q? 1Q?
1S → 0Q? 1Q?
for the desired assignment, certain of which [i.e., 0S,1S → 0Q and 0S,1S → 1Q] fail
to be bijective. Here, it is useful to note that to synchronize these indeterminacies
amounts, tautologically, totherequirementofan“automorphismof≺Q thatinduces
the unique nontrivial automorphism of the set EQ= {0Q,1Q}”. On the other hand,
by the definition of an “inequality”, it is a tautology that such an automorphism of
≺Q cannot exist. Finally, in this context, it is useful to recall that this diﬀerence
between “crushing the set E to a single point” and “symmetrizing without violating
the bijective relationship to E” is precisely the topic of the discussion of [IUTchI],
Remark 4.9.2, (i); [IUTchI], Remark 6.12.4, (i) — cf., especially, [IUTchI], Fig. 4.5.
(ii) The starting point of the theory surrounding the symmetrizing isomor-
phisms of Corollary 3.5, (i), is the connectedness — or “single basepoint”—
observed in the discussion of Remark 2.6.1, (i), together with the compatibility of
this connectedness with a certain F ±
l -symmetry, as discussed in Remark 2.6.2,
98 SHINICHI MOCHIZUKI
(i). These symmetrizing isomorphisms may be applied to labeled copies of vari-
ous objects constructed from MΘ
∗ — e.g., Ψcns(MΘ
∗ ), Gv(MΘ
∗ ), Πμ(MΘ
∗ ) — cf. the
discussion of “conjugate synchronization” in Remark 2.6.1, (i). Note that in the
absence of the F ±
l -symmetry involved, the “single basepoint” under consideration
has a rigidifying eﬀect not only on the various conjugates involved, but also on
the labels under consideration. That is to say, a priori, it is quite possible that
the desired rigidity of the conjugates involved depends on the rigidity of
the labels under consideration.
Indeed, this is precisely what happens when the data that one wishes to synchronize
— i.e., such as monoids, absolute Galois groups, or cyclotomes — consists, for
instance, of an arrow from one label to another, as was [essentially] the case in the
discussion of the combinatorial model of (i). Put another way,
the significance of the F ±
l -symmetry under consideration lies precisely
in the observation that this symmetry serves to eliminate this unwanted
“a priori” possibility.
This is in some sense the central principle illustrated by the combinatorial model
of (i). Put in other words, this “central principle” discussed in (i) may be sum-
marized, in the situation of Corollary 3.5, as follows: the F ±
l -symmetry under
consideration allows one to construct
(a) symmetrizing isomorphisms [cf. Corollary 3.5, (i)]
in a fashion that is compatible with maintaining a
(b) bijective link with the set of labels LabCusp±(ΠX(MΘ
∗ ))
— which is necessary in order to construct the Gaussian monoids [i.e., which
involve distinct values at distinct labels!] in Corollary 3.5, (ii) — all relative to
(c) a single basepoint [i.e., which gives rise to the single topological group
ΠX(MΘ
∗ ) — cf. the discussion of Remark 2.6.2, (i)]
— which is necessary in order to establish conjugate synchronization.
(iii) In the context of Corollary 3.5, (i), one essential aspect of the F ±
l-
symmetry under consideration is that this symmetry arises from a ΔX(MΘ
∗ )-outer
action of ΔC(MΘ
∗ )/ΔX(MΘ
∗ )∼
→ F ±
l [cf. the discussion of Remark 2.6.2, (i)]. That
is to say, the fact that this action may be formulated entirely in terms of conju-
gation by elements of geometric [i.e., “Δ”] fundamental groups — that is to say,
as opposed to arithmetic [i.e., “Π”] fundamental groups — plays a crucial role in
establishing the conjugate synchronization of the various copies of “Gv(MΘ
∗ )”
[and objects constructed from “Gv(MΘ
∗ )”] under consideration [cf. the discussion
of [IUTchI], Remark 6.12.6, (ii)].
(iv) If one thinks of the F ±
l -symmetries that appear in the conjugate synchro-
nizationofCorollary3.5, (i), as“connecting”thevariouscopiesofobjectsatdistinct
evaluation points, then it is perhaps natural to regard the “conjugate synchro-
nization via symmetry” of Corollary 3.5, (i), as a sort of nonarchimedean
version of the “conjugate synchronization via connectedness” discussed in
Remark 2.6.1, (i), which may be thought of as being based on the “archimedean”
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 99
connectedness of the subgraph ΓX ⊆ ΓX [cf. the discussion of Remarks 2.6.1, (i);
2.8.3].
(v) In §4 below, we shall generalize the ideas discussed in the present Remark
3.5.2 concerning conjugate synchronization in the case of v ∈ Vbad to the global
portion, as well as to the portion at good v ∈ Vgood, of a D-Θ±ell-Hodge theater
[cf. the discussions of Remark 2.6.2, (i); Remark 3.8.2 below].
Remark 3.5.3. The delicacy and subtlety of the theory surrounding Corollary
3.5, (i), may be thought of as a consequence of the requirement of simultaneously
satisfying the conditions (a), (b), (c) discussed in Remark 3.5.2, (ii). On the other
hand, ifoneiswillingtoeliminatecondition(c)fromone’sarguments, thenonemay
obtain symmetrizing isomorphisms by simply applying the functors of [IUTchI],
Proposition 6.8, (i), (ii), (iii); [IUTchI], Proposition 6.9, (i), (ii) — i.e., by passing
to D-Θell-bridges or [holomorphic or mono-analytic] capsules or processions. Here,
we observe that this “multi-basepoint” approach to constructing symmetrizing
isomorphisms is compatible with the single basepoint F ±
l -symmetric approach of
Corollary 3.5, (i), relative to the evident “forgetful functors”. We leave the routine
details to the reader.
Corollary 3.6. (Frobenioid-theoretic Gaussian Monoids) Suppose that we
are in the situation of Proposition 3.3, i.e., that
MΘ
∗
= MΘ
∗ (†F
v)
— where †F
is a tempered Frobenioid. We continue to use the conventions
v
introduced in Corollary 3.5 concerning subscripted labels.
(i) (Labels, F ±
l -Symmetries, and Conjugate Synchronization) The
isomorphism of Proposition 3.3, (ii) [or, alternatively, Proposition 1.3, (ii), (iii)],
determines, for each t ∈ LabCusp±(ΠX(MΘ
∗ )), a collection of compatible mor-
phisms
ΠX(MΘ
∗ )t Gv(MΘ
∗ )t
∼
→ Gv(MΘ
∗¨)t
(Ψ†Cv)t
∼
→ Ψcns(MΘ
∗ )t
— which are well-defined up to composition with an inner automorphism of
ΠX(MΘ
∗ ) which is independent of t ∈ LabCusp±(ΠX(MΘ
∗ )) — as well as [F ±
l-
]symmetrizing isomorphisms, induced by the ΔX(MΘ
∗ )-outer action of F ±
∼
=
l
ΔC(MΘ
∗ )/ΔX(MΘ
∗ ) on ΠX(MΘ
∗ ) [cf. Corollary 3.5, (i); Remark 1.1.1, (iv), or,
alternatively, Proposition 1.3, (ii), (iii)], between the data indexed by distinct t ∈
LabCusp±(ΠX(MΘ
∗ )).
(ii) (Gaussian Monoids) For each value-profile ξ [cf. Corollary 3.5, (ii)],
ΨFξ(†F
v) ⊆ ∞ΨFξ(†F
v) ⊆
|t|∈Fl
(Ψ†Cv)|t|
write
100 SHINICHI MOCHIZUKI
for the submonoids determined, respectively, via the isomorphisms (Ψ†Cv)|t|
∼
→
Ψcns(MΘ
∗ )|t| of (i), by the monoids Ψξ(MΘ
∗ ), ∞Ψξ(MΘ
∗ ) of Corollary 3.5, (ii), and
ΨFgau(†F
v) def
= ΨFξ(†F
v) ξ
, ∞ΨFgau(†F
v) def
= ∞ΨFξ(†F
v) ξ
— where ξ ranges over the value-profiles. Thus, each monoid ΨFξ(†F
v) is equipped
with a natural action by Gv(MΘ
∗ )⟨Fl ⟩. Then by composing the Kummer isomor-
phisms discussed in (i) above and Proposition 3.3, (i), (ii), with the restriction
isomorphisms of Corollary 3.5, (ii), one obtains a diagram of compatible mor-
phisms
Πv¨(MΘ
∗¨) = Πv¨(MΘ
∗¨) {Gv(MΘ
∗¨)|t|}|t|∈Fl
∼ → {Gv(MΘ
∗ )|t|}|t|∈Fl
∼
∞Ψ†FΘ
v ,α
→ ∞Ψι
env(MΘ
∗ )∼
→ ∞Ψξ(MΘ
∗ )∼
→ ∞ΨFξ(†F
v)
∼
Ψ†FΘ
v ,α
→ Ψι
env(MΘ
∗ )∼
→ Ψξ(MΘ
∗ )∼
→ ΨFξ(†F
v)
— where the “ ” in the first line [cf. also the second and third “ ” in the sec-
ond line] is as in Corollary 3.5, (ii); we recall the natural inclusion Πv¨(MΘ
∗¨) →
ΠX(MΘ
∗ ) — which is well-defined up to composition with a(n) [single!] inner
automorphism of ΠX(MΘ
∗ ) and compatible [in the evident sense] with the equal-
ities of submonoids involving “Ψ2l·ξ(−)” [cf. Corollary 3.5, (ii)]. For simplicity,
we shall use the notation
Ψ†FΘ
v
∞Ψ†FΘ
v
∼
→ Ψenv(MΘ
∗ )∼
→ Ψgau(MΘ
∗ )∼
→ ΨFgau(†F
v);
∼
→ ∞Ψenv(MΘ
∗ )∼
→ ∞Ψgau(MΘ
∗ )∼
→ ∞ΨFgau(†F
v)
to denote these collections of compatible morphisms.
(iii) (Constant Monoids and Splittings) Relative to the notational con-
ventions adopted thus far [cf. also Corollary 3.5, (iii)], the diagonal submonoid
(Ψ†Cv)⟨|Fl|⟩ determines — i.e., may be thought of as the graph of — an isomor-
phism of monoids
(Ψ†Cv)0
∼
→ (Ψ†Cv)⟨Fl ⟩
that is compatible with the respective labeled Gv(MΘ
∗ )-actions. Moreover, the
splittings of Corollary 3.5, (iii), determine splittings up to torsion of each of the
[“Frobenioid-theoretic”] Gaussian monoids
ΨFξ(†F
v) = (Ψ×
†Cv)⟨Fl ⟩· Im(ξ)N
, ∞ΨFξ(†F
v) = (Ψ×
†Cv)⟨Fl ⟩· Im(ξ)Q≥0
— where “Im(ξ)” denotes the image of ξ via the isomorphisms discussed in (ii) —
which are compatible, relative to the various isomorphisms of the third display
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 101
of (ii), with the splittings up to torsion of Proposition 3.1, (i); Proposition 3.3, (i);
Corollary 3.5, (iii).
Proof. The various assertions of Corollary 3.6 follow immediately from the defini-
tions and the references quoted in the statements of these assertions. ⃝
Remark 3.6.1. The “Galois compatibility” denoted by the “ ” in the third
display of Corollaries 3.5, (ii); 3.6, (ii) — involving the monoids “∞Ψ” [i.e., not
just the monoids “Ψ”!] — corresponds precisely to the “Galois functoriality” [cf.
Fig. 1.5] of the discussion of Remark 1.12.4.
Remark 3.6.2. The diagram in the third display of Corollary 3.6, (ii) —
which may be thought of as a sort of concrete realization of the principle of Galois
evaluation discussed in Remark 1.12.4 [cf. also Remark 3.6.1] — will play a central
role in the theory of the present series of papers. Thus, it is of interest to pause
here to discuss various aspects of the significance of this diagram.
Frobenioid-theoretic
theta monoids
Kummer
=⇒
group-theoretic
theta monoids
Galois ⇓ evaluation
Frobenioid-theoretic
Gaussian monoids
[i.e., theta values]
forget!
⇐=
group-theoretic
Gaussian monoids
[i.e., theta values]
Fig. 3.1: Kummer theory and Galois evaluation
(i) The left-hand, central, and right-hand portions of this diagram are summa-
rized, at a more conceptual level, in Fig. 3.1 above — that is to say, if one thinks
of the mono-theta environments “MΘ
∗ ” involved as arising group-theoretically [i.e.,
from´ etale-like objects, which is, of course, always the case up to isomorphism! —
cf. the situation discussed in Corollary 3.7, (i), below], then these portions corre-
spond, respectively, to the arrows “=⇒”, “⇓”, and “⇐=” in Fig. 3.1. Here, we note
that the final operation of “forgetting” [i.e., “⇐=”] may be thought of as the op-
eration of forgetting the group-theoretic — i.e., “anabelian” — construction of the
Gaussian monoids, so as to obtain “abstract monoids stripped of any information
concerning the group-theoretic algorithms used to construct them” — which we
refer to as “post-anabelian” [cf. the discussion of Remark 1.11.3, (iii); Corollary
3.7, (i), below; the constructions of Definition 3.8 below]. On the other hand, the
composite of the arrows “=⇒” and “⇓” may be thought of as a sort of
comparison isomorphism between “Frobenius-like” [i.e., “Frobenioid-
theoretic”] and“´ etale-like” [i.e., “group-theoretic”] structures
102 SHINICHI MOCHIZUKI
— cf. the discussion of [FrdI], Introduction; [IUTchI], Corollaries 3.8, 3.9. In this
context, it is useful to recall that the comparison isomorphism of the “classical”
scheme-theoretic version of Hodge-Arakelov theory [cf. [HASurI], Theorem A] is
obtained precisely by evaluating theta functions and their derivatives at certain
torsion points of an elliptic curve.
(ii) The existence of both “Frobenius-like” and “´ etale-like” structures in the
theory of the present series of papers, together with the somewhat complicated
theory of comparison isomorphisms as discussed above in (i), prompts the following
question:
Whatarethevariousmerits anddemerits of“Frobenius-like”and“´ etale-
like” structures that require one to avail oneself of both types of structure
in the theory of the present series of papers [cf. Fig. 3.2 below]?
On the one hand, unlike Frobenius-like structures, ´ etale-like structures — in the
form of´ etale or tempered fundamental groups [such as Galois groups] — have the
crucial advantage of being functorial or invariant with respect to various non-
ring/scheme-theoretic filters between distinct ring/scheme theories. In the
context of the present series of papers, the main examples of this phenomenon
consist of the Θ-link [cf., e.g., [IUTchI], Corollary 3.7] and the log-wall [cf. [Ab-
sTopIII], §I1, §I4; this theory will be incorporated into the present series of papers
in [IUTchIII]]. Another important characteristic of the ´ etale-like structures consti-
tuted by ´ etale or tempered fundamental group is their “remarkable rigidity” — a
property that is exhibited explicitly [cf., e.g., the theory of [EtTh]; [AbsTopIII]]
by various anabelian algorithms that may be applied to construct, in a “purely
group-theoretic fashion”, various structures motivated by conventional scheme
theory. By contrast, the Frobenius-like structures constituted by various abstract
monoids — which typically give rise to various Frobenioids — satisfy the crucial
property of not being subject to such rigidifying anabelian algorithms that re-
late various ´ etale-like structures to conventional scheme theory. It is precisely this
property of such abstract monoids that allows one to use these abstract monoids
to construct such non-scheme-theoretic filters as the Θ-link [cf. [IUTchI],
Corollary 3.7] or the log-wall of the theory of [AbsTopIII]. Here, it is interesting to
observe that
thesemerits/demeritsof´ etale-likeandFrobenius-likestructuresplaysome-
what complementary roles with respect to binding/not binding the
structures under consideration to conventional scheme theory.
Finally, we note that Kummer theory serves the crucial role [cf. the discussion
of (i)] of relating [via various comparison isomorphisms — cf. (i)] — within a given
Hodge theater — potentially non-scheme-theoretic Frobenius-like structures to
´ etale-like structures which are subject to anabelian rigidifications that bind them
to conventional scheme theory.
(iii) If one composes the correspondence “q
v
→ Θ
v” [cf. the discussion of
[IUTchI], Remark 3.8.1, (i)] constituted by the Θ-link — i.e., which relates the
“(n + 1)-th generation q-parameter” to the “n-th generation Θ-function” — with
the composite of the arrows “=⇒”, “⇓”, and “⇐=” of Fig. 3.1, then one obtains a
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 103
correspondence
q
v
→ qj2
v 1≤j≤l
[cf. Remark 2.5.1, (i)]. In fact, in the theory of the present series of papers, it is
ultimately this “modified version of the Θ-link” — i.e., which takes into account the
Hodge-Arakelov-theoretic evaluation theorydeveloped so far in §2 and the present §3
— that will be of interest to us. The theory of this “modified version of the Θ-link”
will constitute one of the main topics treated in §4 below. Here, we observe that the
above correspondence may be thought of as a sort of “abstract, combinatorial
Frobenius lifting” — i.e., as a sort of “homotopy” between
· the identity q
v
→ q
v
[i.e., which corresponds to “characteristic zero”]
and
· the purely monoid-theoretic/highly non-scheme-theoretic corre-
spondence q
v
→ q(l )2
[i.e., which corresponds to the “positive character-
v
istic Frobenius morphism”].
Moreover, we recall [cf. the discussion of Remark 2.6.3] that the collection of ex-
ponents {j2}1≤j≤l that appear in this “abstract, combinatorial Frobenius lifting”
is highly distinguished — hence, in particular, far from arbitrary!
´ etale-like structures Frobenius-like structures
functoriality/invariance
with respect to —
log-wall, Θ-link
rigidified relationship via
Kummer theory—
+ anabelian geom.
to conventional arith. geom.
lack of rigidification allows construction
— of non-scheme-theoretic filters,
such as log-wall, Θ-link
Fig. 3.2:
´
Etale-like versus Frobenius-like structures
(iv) In the context of the discussion of (i), it is of interest to recall that vari-
ous “Grothendieck Conjecture-type results” in anabelian geometry [e.g., over p-adic
local fields and finite fields] — i.e., which may be thought of as comparison iso-
morphisms between polynomial-function-theoretic and group-theoretic collections of
morphisms — are obtained precisely by combining various considerations particular
104 SHINICHI MOCHIZUKI
to the situation of interest with the “Galois evaluation” via Kummer theory
of polynomial functions or diﬀerential forms at various rational points — cf. the
theory of [pGC]; [Cusp], §2.
Remark 3.6.3. Remark 3.6.2.
Before proceeding, we make some observations concerning base-
points in the context of the “non-ring/scheme-theoretic filters” discussed in
(i) First, let us recall from the elementary theory of´ etale fundamental groups
that the fiber functor associated to a basepoint is defined by considering the points
of a finite ´ etale covering valued in some separably closed field that lie over a fixed
point [valued in the same separably closed field] of the base scheme over which
the covering is given. Thus, for instance, when this base scheme is the spectrum
of a field, the finite set of points associated by the fiber functor to a finite ´ etale
covering is obtained by considering the various ring homomorphisms from this field
into some separably closed field. In particular, it follows that
the conventional scheme-theoretic definition of a basepoint [in the form
of a fiber functor] depends, in an essential fashion, on the ring/scheme
structure of the rings or schemes under consideration.
One immediate consequence of these elementary considerations — which is of cen-
tral importance in the theory of the present series of papers — is the following ob-
servation concerning the “non-ring/scheme-theoretic filters” discussed in Remark
3.6.2, which relate one ring to another in a fashion that is incompatible with the
respective ring structures:
The distinct ring structures on either side of one of the “non-ring/
scheme-theoretic filters” discussed in Remark 3.6.2 — i.e., the log-wall of
[AbsTopIII] and the Θ-link of [IUTchI], Corollary 3.7 — give rise to dis-
tinct, unrelated basepoints [cf. the discussion of [AbsTopIII], Remark
3.7.7, (i)].
In some sense, the above discussion may be thought of as an “expanded, leisurely
version” of an observation made at the beginning of the discussion of [AbsTopIII],
Remark 3.7.7, (i).
(ii) The observations of (i) also apply to the“N-th power morphisms” [where
N > 1] — i.e., “morphisms of Frobenius type” — that appear in the theory of
Frobenioids [cf. [FrdI], [FrdII], [EtTh]]. That is to say, in the context of the
tempered Frobenioids that appear in the theory of [EtTh], §5, such “morphisms of
Frobenius type” [i.e., “N-th power morphisms” regarded as morphisms containedin
the underlying categories associated to these tempered Frobenioids] induce “N-th
power morphisms” between various monoids [arising from the Frobenioid structure]
isomorphic to O◃
Kv. In particular,
these N-th power morphisms of monoids fail [since N > 1] to preserve
the ring structure of Kv, hence give rise to distinct, unrelated base-
points on the domain and codomain objects of the original “morphism of
Frobenius type” [cf. the discussion of (i)].
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 105
On the other hand, let us observe that unlike the situations considered in the dis-
cussion of (i), the considerations of the present discussion involving N-th power
morphisms take place in a fashion that is compatible with the projection func-
tor to the base category of the Frobenioid. One important consequence of this last
observation is that unlike the situations discussed in (i) involving the log-wall and
the Θ-link in which one must consider arbitrary isomorphisms of topologi-
cal groups between the ´ etale [or tempered] fundamental groups that arise in the
domain and the codomain of the operation under consideration,
in the situation of the present discussion of N-th power morphisms, the
“distinct, unrelated basepoints” that arise only give rise to inner auto-
morphisms of the topological group determined by [i.e., roughly speak-
ing, the “fundamental group” of] the base category.
This phenomenon may be thought of as a reflection of the fact that the application
of an N-th power morphism is somewhat “milder” than the log-wall or Θ-link
considered in (i) in that it only involves an operation — i.e., raising to the N-th
power — that is “algebraic”, in the sense that it is defined with respect to the
ring structure of the ring [e.g., Kv] involved. This somewhat “milder nature” of
an N-th power morphism allows one to consider N-th power morphisms within a
single category [namely, the tempered Frobenioid under consideration] which can
be defined in terms of [formal] flat OKv-schemes [cf. the point of view of [EtTh],
§1]. By contrast, the operation inherent in the log-wall or Θ-link considered in
(i) is much more drastic and arithmetic [i.e., “non-algebraic”] in nature, and it
is diﬃcult to see how to fit such an operation into a single category that somehow
“extends” the tempered Frobenioid under consideration in a fashion that “lies over”
the same base category as the tempered Frobenioid — cf., e.g., Remark 1.11.2, (ii),
in the case of the Θ-link; the discussion of [AbsTopIII], Remark 3.7.7, in the case
of the log-wall. Put another way,
the highly nontrivial study of the mathematical structures“generated by
the log-wall and Θ-link” is, in some sense, one of the main themes of the
theory of the present series of papers
— cf., especially, the theory of [IUTchIII]!
Remark 3.6.4. Since the theory of mono-theta environments developed in
[EtTh] plays a fundamental role in the theory of the present paper — cf., e.g.,
Corollaries 1.12, 2.8, 3.5, 3.6 — it is of interest to pause to review the relationship
of the theory of [EtTh] to the theory developed so far in the present paper.
(i) The various remarks following [EtTh], Corollary 5.12, discuss the signifi-
canceofthevariousrigidity propertiesofamono-thetaenvironmentthatareverified
in [EtTh]. The logical starting point of this discussion is the situation considered
in [EtTh], Remarks 5.12.1, 5.12.2, consisting of an abstract category which is only
known up to isomorphism [i.e., up to an indeterminate equivalence of categories],
and in which each of the objects is only known up to isomorphism. The main
example of such a category, in the context of the theory of [EtTh], is a tempered
Frobenioid of the sort considered in Propositions 3.3, 3.4; Corollary 3.6. The situa-
tion of [EtTh], Remarks 5.12.1, 5.12.2, in which each of the objects in the category
106 SHINICHI MOCHIZUKI
is only known up to isomorphism, contrasts sharply with the notion of a system, or
tower, of [specific!] coverings — e.g., of the sort that appears in Kummer theory, in
which the coverings are related by [specific!] N-th power morphisms. Indeed, the
various rigidity properties verified in [EtTh] are of interest precisely because
they yield eﬀective reconstruction algorithms for reconstructing the
various structures of interest in a fashion that is invariant with respect
to the indeterminacies that arise from a situation in which each of the
objects in the category is only known up to isomorphism.
This prompts the following question:
What is the fundamental reason, in the context of the theory of the
present series of papers, that one must work under the assumption that
each of the objects in the category is only known up to isomorphism,
thus requiring one to avail oneself of the rigidity theory of [EtTh]?
To understand the answer to this question, let us first observe that Kummer towers
involving [specific!] N-th power morphisms are constructed by using the multi-
plicative structure of the “rational functions” [such as the pv-adic local field Kv]
under consideration. That is to say, the N-th power morphisms are compatible
with the multiplicative structure, but not the additive structure of such rational
functions. On the other hand, ultimately,
when, in [IUTchIII], we consider the theory of the log-wall [cf. [Ab-
sTopIII]], it will be of crucial importance to consider, within each Hodge
theater, the ring structure [i.e., both the multiplicative and additive struc-
tures] of the fields Kv.
That is to say, without the ring structure on Kv, one cannot even define the pv-
adic logarithm! Put another way, the N-th power morphisms that appear in a
Kummer tower may be thought of as “Frobenius morphisms of a sort” that relate
distinct ring structures — i.e., since the N-th power morphism fails to be compatible
with addition! In particular, the distinct ring structures that exist in the domain
and codomain of such a “Frobenius morphism” necessarily give rise to distinct,
unrelated basepoints [cf. the discussion of Remark 3.6.3, (ii)] — i.e., at an ab-
stract category-theoretic level, to objects which are only known up to isomorphism!
This is what requires one to contend with the indeterminacies discussed in [EtTh],
Remarks 5.12.1, 5.12.2.
(ii) The theory of [EtTh] may be summarized as asserting that one may re-
construct various structures of interest from a mono-theta environment without
sacrificing certain fundamental rigidity properties, even in a situation subject to
certain indeterminacies [cf. (i)]. Moreover, mono-theta environments serve as a
sort of bridge [cf. [EtTh], Remark 5.10.1] between tempered Frobenioids — i.e.,
“Frobenius-like structures” [cf. Remark 3.6.2] — as in Propositions 3.3, 3.4; Corol-
lary 3.6, on the one hand, and tempered fundamental groups [cf. Proposition 3.4]
— i.e.,“´ etale-like structures [cf. Remark 3.6.2] — on the other.
(iii) One central feature of the theory of [EtTh] is an explanation of the special
role played by the first power of the [reciprocal of the l-th root of the] theta
function, a role which is reflected in the theory of cyclotomic rigidity developed
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 107
in [EtTh] [cf. [EtTh], Introduction]. Note that the operation of Galois evaluation
is necessarily linear [cf. the discussion of Remark 1.12.4]. This linearity may be
seen in the linearity of the arrows “=⇒”, “⇓”, and “⇐=” of Fig. 3.1. In particular,
these arrows are compatible with the ring structure on the constants [i.e., “Kv”]
— a property that will be of crucial importance when, in [IUTchIII], we consider
the theory of the log-wall [cf. the discussion of (i) above]. Moreover, this linearity
property of the operation of Galois evaluation implies that
the first power of the theta values of the [reciprocal of the l-th root of
the] theta function “inherits”, so to speak, the special role played by the
first power of the [reciprocal of the l-th root of the] theta function.
This observation is interesting in light of the discussions of Remarks 2.6.3; 3.6.2,
(iii).
(iv) In the context of (iii), we note that the various theta monoids discussed in
Propositions 3.1, 3.3, as well as the various Gaussian monoids discussed in Corol-
laries 3.5, 3.6, involve arbitrary powers/roots of the [reciprocal of the l-th root
of the] theta function. Nevertheless, it is important to remember that
in order to apply the Θ-link — which requires one to work with “Frobe-
nius-like structures” [cf. the discussion of Remark 3.6.2, (ii)] — it is
necessary to consider the operation of Galois evaluation summarized in
Fig. 3.1 applied to the first power of the [reciprocal of the l-th root
of the] Frobenioid-theoretic theta function in order to avail oneself of the
cyclotomic rigidity furnished by the delicate bridge constituted by the
mono-theta environment
— cf. (ii) above. That is to say, the “narrow bridge” aﬀorded by the mono-theta
environment betweenthe worlds of “Frobenius-like” and “´ etale-like”structures may
only be crossed by the first power of the [reciprocal of the l-th root of the] theta
function and its theta values. Put another way,
from the point of view of the´ etale-like portion [i.e., “group-theoretic”
portion] of the operation of Galois evaluation summarized in Fig. 3.1, the
N-th power of the [reciprocal of the l-th root of the] Frobenioid-theoretic
theta function, for N > 1, is only defined as the N-th power “(−)N”
of the first power of the [reciprocal of the l-th root of the] Frobenioid-
theoretic theta function.
That is to say, from the point of view of the ´ etale-like portion of the operation of
Galois evaluation summarized in Fig. 3.1, the N-th power of the [reciprocal of
the l-th root of the] Frobenioid-theoretic theta function, for N > 1 — hence, in
particular, the Θ-link— may only be calculated by forming the N-th power
“(−)N” of the first power of the [reciprocal of the l-th root of the] Frobenioid-
theoretic theta function.
(v)Thenecessityofworkingwith“Frobenius-likestructures”[cf. thediscussion
of (iv)] may also be thought of as the necessity of working with the various post-
anabelian monoids arising from the group-theoretic “anabelian” algorithms that
appear in the operation of Galois evaluation [cf. the discussion of Remark 3.6.2,
108 SHINICHI MOCHIZUKI
(i)]. In the context of this observation, it is useful to recall that from the point of
view of the theory of §1,
the “narrow bridge” furnished by [for instance, the cyclotomic rigidity
of] a mono-theta environment satisfies the crucial property of multira-
diality [cf. Corollaries 1.10, 1.12] — i.e., of being “horizontal” with
respect to the “connection structure” determined by the formulation
of this multiradiality [cf. the point of view discussed in Remarks 1.7.1,
1.9.2].
Put another way, to work with powers other than the first power of the [reciprocal of
the l-th root of the] theta function or its theta values gives rise to structures which
are “not horizontal” with respect to this “connection structure”. This point of
view is consistent with the point of view of Remark 3.6.5, (iii), below. A similar
observation concerning multiradiality will also apply to the “multiradial versions of
the Gaussian monoids” that will be constructed in [IUTchIII] [cf. Remark 3.7.1
below].
Remark 3.6.5. In light of the central role played by mono-theta-theoretic
cyclotomic rigidity in the discussion of Remark 3.6.4, we pause to make some
observations — of a somewhat more philosophical nature — concerning this topic.
(i) First of all, we observe that
acyclotome maybethoughtofasasortof“skeleton of the arithmetic
holomorphic structure” under consideration
— cf. the discussion of Remark 1.11.6. Indeed, this point of view may be thought
of as being motivated by the situation at archimedean primes, where the circle “S1”
may be thought of as a sort of “representative skeleton of C×”. This point of view
will play a central role in the remainder of the discussion of the present Remark
3.6.5, as well as in the discussion of Remark 3.8.3 below.
(ii) In the theory of [EtTh],
(a) the commutator structure [−
,−] of the theta group plays a central
role in the theory of mono-theta-theoretic cyclotomic rigidity
— cf. [EtTh], Introduction; [EtTh], Remark 2.19.2. On the other hand, in the
classical theory of algebraic theta functions
(b) thecommutator structure [−
,−] of the theta groupplaysacentralrole
in the theory via the observation that this commutator structure implies
the irreducibility of certain representations of the theta group.
At first glance, these two applications (a), (b) of the commutator structure [−
,−]
of the theta group may appear to be unrelated. In fact, however, they may both
be understood as examples of the following phenomenon:
(c) the commutator structure [−
,−] of the theta group may be thought
of as a sort of concrete embodiment of the “coherence of holomorphic
structures”.
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 109
Indeed, as discussed in [EtTh], Introduction, from the point of view of the scheme-
theoreticHodge-Arakelovtheoryof[HASurI],[HASurII],theirreduciblerepresenta-
tions that appear in the classical theory of algebraic theta functions as submodules
ofthemoduleofallset-theoreticfunctionsonthel-torsionpointsofanellipticcurve
[cf. (b)] may be thought of, for instance, when l is large, as discrete analogues of
the submodule of “holomorphic functions” within the module of all real analytic
functions. On the other hand, if one thinks of cyclotomes as “skeleta of arithmetic
holomorphic structures” [cf. (i)], then the theory of conjugate synchronization
[cf. Remark 3.5.2, as well as Remark 3.8.3 below] — applied, for instance, in the
case of cyclotomes — may be thought of as a sort of “discretely parametrized” [in
the sense that it is indexed by torsion points] coherence of arithmetic holo-
morphic structures, which is obtained by working with the connected subgraph
ΓX ⊆ ΓX [cf. Remark 2.6.1, (i)]. In this context, mono-theta-theoretic cyclotomic
rigidity [cf. (a)] may be thought of as a sort of “continuously parametrized version”
¨
[i.e., supported on
Y
v, as opposed to a finite set of torsion points] of this coherence
of arithmetic holomorphic structures. Finally, we recall that the interaction — i.e.,
via restriction operations — between these “discrete” and “continuous” versions
of the “coherence of arithmetic holomorphic structures” plays a central role in the
theory of Galois evaluation given in Corollaries 2.8, (i); 3.5, (ii); 3.6, (ii).
(iii) If one thinks of cyclotomes at localizations [say, at v ∈ Vbad] of a number
field [i.e., K] as local skeleta of the arithmetic holomorphic structure [cf. (i)], then
the mono-theta-theoretic cyclotomic rigidity may be thought of as a
sort of “local uniformization” of a number field [cf. the exterior cyclo-
tomeofamono-thetaenvironmentthatarisesfromatemperedFrobenioid,
as in Proposition 1.3, (i)] via a local portion [cf. the interior cyclotome
in the situation of Proposition 1.3, (i)] of the geometric tempered funda-
mental group Δv associated to a certain covering of the once-punctured
elliptic curve XF [cf. Definition 2.3, (i); [IUTchI], Definition 3.1, (e)].
Since the cyclotomic rigidity isomorphism arising from mono-theta-theoretic cyclo-
tomic rigidity may be thought of as the “cyclotomic portion” of the theta function,
mono-theta-theoretic cyclotomic rigidity may be interpreted as the statement that
the theta function constructed from a mono-theta environment is free of any Z×
-
power indeterminacies. Moreover, if one takes this point of view, then
constant multiple rigidity may be thought of as the statement that
the above “local uniformization” is suﬃciently rigid as to be free of any
constant multiple indeterminacies.
Here, it is useful to recall that the once-punctured elliptic curve XF on the number
field F that occurs in the theory of the present series of papers may be thought of as
being analogous to the nilpotent ordinary indigenous bundles on a hyperbolic
curve in positive characteristic in p-adic Teichm¨ uller theory [cf. the discussion of
[AbsTopIII], §I5]. That it to say, from this point of view, the “local uniformiza-
tions” of the above discussion may be thought of as corresponding to the local
uniformizations via canonical coordinates of p-adic Teichm¨ uller theory [cf.,
e.g., [pTeich], §0.9], which are also “suﬃciently rigid” as to be free of any Z×-power
or constant multiple indeterminacies. Here, mono-theta-theoretic cyclotomic rigid-
ity may be thought of as corresponding to the Kodaira-Spencer isomorphism
110 SHINICHI MOCHIZUKI
[associated to the Hodge section of the canonical indigenous bundle], which, in some
sense, may be thought of as the “skeleton” of the local uniformizations of p-adic
Teichm¨ uller theory. Also, it is useful to recall in this context that the canonical
coordinates of p-adic Teichm¨ uller theory are constructed by considering invariants
with respect to certain canonical Frobenius liftings. Put another way, the technique
of considering Frobenius-invariants allows one to pass, in a canonical way, from
objects defined modulo p to objects defined modulo higher powers of p. Since the
various Θ-links of the Frobenius-picture may be regarded as corresponding to the
various transitions from “mod pn to mod pn+1” [where n ∈ N] in the theory of
Witt vectors [cf. the discussion of [IUTchI], §I4; [IUTchIII], Remark 1.4.1, (iii)],
it is natural to regard, in the context of the canonical splittings furnished by the
´ etale-picture [cf. the discussion of [IUTchI], §I1],
the multiradiality of the formulation of mono-theta-theoretic cyclotomic
rigidity and constant multiple rigidity given in Corollary 1.12 as corre-
sponding to the Frobenius-invariant nature of the canonical coordinates
of p-adic Teichm¨ uller theory.
Finally, in this context, we observe that it is perhaps natural to think of the dis-
crete rigidity of the theory of [EtTh] as corresponding to the fact that the canoni-
cal coordinates of p-adic Teichm¨ uller theory, which a priori may only be constructed
as PD-formal power series, may in fact be constructed as power series in the
usual sense, i.e., elements of the completion O of the local ring at the point under
consideration. Indeed, the discrete rigidity of [EtTh] implies that one may restrict
oneself to working with the usual theta function, canonical multiplicative coordi-
nates [i.e., “U”], and q-parameters on appropriate tempered coverings of the Tate
curve, all of which, like the power series arising from canonical parameters in p-adic
Teichm¨ uller theory, give rise to “functions on suitable formal schemes” in the sense
of classical scheme theory. By contrast, if this discrete rigidity were to fail, then one
would be obliged to work in an “a priori profinite” framework that involves, for in-
stance, Z-powers of “U” and “q”[cf. [EtTh], Remarks1.6.4, 2.19.4]. SuchZ-powers
appear naturally in the Z-modules that arise [e.g., as cohomology modules] in the
Kummer theory of the theta function and may be thought of as corresponding to
PD-formal power series in the sense that arbitrary O-powers of canonical parame-
ters [say, for simplicity, at non-cuspidal ordinary points of a canonical curve], which
arise naturally when one considers such parameters additively [cf. the discussion
of “canonical aﬃne coordinates” in [pOrd], Chapter III], cannot be defined if one
restricts oneself to working with conventional power series — i.e., such O-powers
may only be defined if one allows oneself to work with PD-formal power series.
Corollary 3.7. (Group-theoretic Gaussian Monoids and Uniradiality)
Suppose that we are in the situation of Proposition 3.4, i.e., in the following, we
consider the full poly-isomorphism
MΘ
∗ (Πv)∼
→ MΘ
∗ (†F
v)
— where MΘ
∗ (Πv) is the projective system of mono-theta environments arising from
the algorithm of Proposition 1.2, (i) [cf. also Proposition 1.5, (i)]; †F
is a tem-
v
pered Frobenioid as in Proposition 3.3 — of projective systems of mono-
theta environments. When “MΘ
∗ ” is taken to be MΘ
∗ (†F
v), we shall denote the
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 111
resulting “MΘ
∗¨” by MΘ
∗¨(†F
v) [cf. Definition 2.7, (ii)]. When “MΘ
∗ ” is taken to
be MΘ
∗ (Πv), we shall identify Πv¨(MΘ
∗¨) and Gv(MΘ
∗¨) [cf. Definition 2.7, (ii)]
with Πv¨ and Gv(Πv¨) [cf. Corollary 2.5, (i)], respectively, via the tautological
isomorphisms Πv¨(MΘ
∗¨)∼
→ Πv¨
, Gv(MΘ
∗¨)∼
→ Gv(Πv¨). Finally, we shall follow
the notational conventions of Corollaries 3.5, 3.6 with regard to the subscripts
“|t|”, for |t| ∈ |Fl|, and “⟨Fl ⟩”.
(i) (From Group-theoretic to Post-anabelian Gaussian Monoids) Each
isomorphism of projective systems of mono-theta environments MΘ
∗ (Πv)∼
→ MΘ
∗ (†F
v)
induces compatible [in the evident sense] collections of isomorphisms
Πv¨ {Gv(Πv¨)|t|}|t|∈Fl
∞Ψι
env(MΘ
∗ (Πv))∼
→ ∞Ψξ(MΘ
∗ (Πv))
Ψι
env(MΘ
∗ (Πv))∼
→ Ψξ(MΘ
∗ (Πv))
∼ → {Gv(MΘ
∗¨(†F
v))|t|}|t|∈Fl
∼ → {Gv(MΘ
∗ (†F
v))|t|}|t|∈Fl
∼
→ ∞Ψξ(MΘ
∗ (†F
v))∼
→ ∞ΨFξ(†F
v)
∼
→ Ψξ(MΘ
∗ (†F
v))∼
→ ΨFξ(†F
v)
and
Gv(Πv¨)∼
→ Gv(Πv¨)⟨Fl ⟩
Ψι
env(MΘ
∗ (Πv))× ∼
→ Ψξ(MΘ
∗ (Πv))×
∼
→ Gv(MΘ
∗¨(†F
v))⟨Fl ⟩
∼
→ Gv(MΘ
∗ (†F
v))⟨Fl ⟩
∼
→ Ψξ(MΘ
∗ (†F
v))× ∼
→ ΨFξ(†F
v)×
— where the upper left-hand portion of the first display [involving “ ”] is
obtained by applying the third display [involving “ ”] of Corollary 3.5, (ii), in
the case where “MΘ
∗ ” is taken to be MΘ
∗ (Πv); the isomorphisms that relate the
upper left-hand portion of the first display to the lower right-hand portion of the
first display arise from the functoriality of the algorithms involved, relative to
isomorphisms of projective systems of mono-theta environments; the lower right-
hand portion of the first display is obtained by applying the right-hand portion
112 SHINICHI MOCHIZUKI
of the third display of Corollary 3.6, (ii), in the case where “MΘ
∗ ” is taken to be
MΘ
∗ (†F
v); the second display is obtained from the first display by considering the
units [denoted by means of a superscript “×”].
(ii) (Uniradiality of Gaussian Monoids) If we write ΨFξ(†F
v)×μ for the
ind-topological monoid obtained by forming the quotient of ΨFξ(†F
v)× by its torsion
subgroup, then the functorial algorithms
Πv → Ψgau(MΘ
∗ (Πv)); Πv → ∞Ψgau(MΘ
∗ (Πv))
— where we think of Ψgau(MΘ
∗ (Πv)), ∞Ψgau(MΘ
∗ (Πv)) as being equipped with their
natural splittings up to torsion [cf. Corollary 3.5, (iii)] and, in the case of
Ψgau(MΘ
∗ (Πv)), the natural Gv(Πv¨)-action [cf. Corollary 3.5, (ii)] — obtained by
composing the algorithms of Proposition 1.2, (i); Corollary 3.5, (ii), (iii), depend
on the cyclotomic rigidity isomorphism of Corollary 1.11, (b) [cf. Remark
1.11.5, (ii); the use of the surjection of Remark 1.11.5, (i), in the algorithms of
Proposition 3.1, (ii), and Corollary 3.5, (ii)], hence fail to be compatible, rela-
tive to the displayed diagrams of (i), with automorphisms of [the underlying pair,
consisting of an ind-topological monoid equipped with the action of a topological
group, determined by] the pair
Gv(MΘ
∗ (†F
v))⟨Fl ⟩ ΨFξ(†F
v)×μ
which arise from automorphisms of [the underlying pair, consisting of an ind-
topological monoid equipped with the action of a topological group, determined by]
the pair Gv(MΘ
∗ (†F
v))⟨Fl ⟩ ΨFξ(†F
v)× [cf. Remarks 1.11.1, (i), (b); 1.8.1] —
in the sense that this algorithm, as given, only admits a uniradial formulation [cf.
Remarks 1.11.3, (iv); 1.11.5, (ii)].
Proof. The various assertions of Corollary 3.7 follow immediately from the defini-
tions and the references quoted in the statements of these assertions. ⃝
Remark 3.7.1. One central consequence of the theory to be developed in
[IUTchIII] [cf. Remarks 2.9.1, (iii); 3.4.1, (ii)] is the result that,
by applying the theory of log-shells [cf. [AbsTopIII]], one may modify the
algorithms of Corollary 3.7, (ii), in such a way as to obtain algorithms
for computing the Gaussian monoids that [yield functors which] are
manifestly multiradially defined
— albeit at the cost of allowing for certain [relatively mild!] indeterminacies.
The following definition in some sense summarizes the theory of the present
§3.
Definition 3.8. Many of the “monoids equipped with a Galois action” that
appear in the discussion of the present §3 may be thought of as giving rise to
Frobenioids, as follows.
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 113
(i) Each of the monoids equipped with a ΠX(MΘ
∗ )-action
ΠX(MΘ
∗ ) Ψcns(MΘ
∗ ); ΠX(MΘ
∗ ) Ψ†Cv
of Propositions 3.1, (ii); 3.3, (ii), gives rise to a pv-adic Frobenioid of monoid type
Z [cf. [FrdII], Example 1.1, (ii)]
Fcns(MΘ
∗ ); F†Cv
whose divisor monoid associates to every object of Btemp(ΠX(MΘ
∗ ))0 a monoid
isomorphic to Q≥0. It follows immediately from the construction of the data
“ΠX(MΘ
∗ ) Ψ†Cv” [cf. Example 3.2, (ii)] that one has a tautological isomor-
phism of Frobenioids
†Cv
∼ → F†Cv
[cf. thediscussionof[IUTchI],Example3.2, (iii), (iv)], whichweshallusetoidentify
these two Frobenioids. Thus, the isomorphism of monoids of Proposition 3.3, (ii),
may be interpreted as an isomorphism of Frobenioids
†Cv
∼ → Fcns(MΘ
∗ )
—whichalsoadmits[indeed,induces]a“mono-analytic version”†C⊢
∼ → F⊢
v
cns(MΘ
∗ )
[cf. the category “C⊢
v ” of [IUTchI], Example 3.2, (iv)]. This mono-analytic version
admits a “labeled version” [cf. Remark 3.8.1 below]
(†C⊢
v )|t|
∼
→ (F⊢
cns(MΘ
∗ ))|t|
— cf. Corollary 3.6, (i). Finally, one has Frobenioid-theoretic interpretations
(F⊢
cns(MΘ
∗ ))⟨|Fl|⟩; (F⊢
cns(MΘ
∗ ))0
(†C⊢
v )⟨|Fl|⟩; (†C⊢
v )0
∼
→ (F⊢
cns(MΘ
∗ ))⟨Fl ⟩
∼
→ (†C⊢
v )⟨Fl ⟩
of the constructions of Corollary 3.5, (iii); 3.6, (iii).
(ii) Each of the monoids equipped with a topological group action
Gv(MΘ
∗¨) Ψι
env(MΘ
∗ ); Gv(MΘ
∗¨) Ψ†FΘ
v ,α
Gv(MΘ
∗¨)⟨Fl ⟩ Ψξ(MΘ
∗ ); Gv(MΘ
∗ )⟨Fl ⟩ ΨFξ(†F
v)
[cf. Proposition 3.1, (i); Proposition 3.3, (i); Corollary 3.5, (ii); Corollary 3.6, (ii)]
gives rise to a pv-adic Frobenioid of monoid type Z [cf. [FrdII], Example 1.1, (ii)]
Fι
env(MΘ
∗ ); F†FΘ
v ,α; Fξ(MΘ
∗ ); FFξ(†F
v)
whose divisor monoid associates to every object of Btemp(Gv(−))0 [where “(−)” is
MΘ
∗¨ or MΘ
∗ ] a monoid isomorphic to N. Moreover, each of these Frobenioids is
114 SHINICHI MOCHIZUKI
equipped with a collection of splittings [cf. Proposition 3.1, (i); Proposition 3.3, (i);
Corollary 3.5, (iii); Corollary 3.6, (iii)]. Also, we shall write
Fenv(MΘ
∗ ) def
= Fι
env(MΘ
∗ )
def
; F†FΘ
v
ι
= F†FΘ
v ,α
α
Fgau(MΘ
∗ ) def
= Fξ(MΘ
∗ ) ξ
; FFgau(†F
v) def
= FFξ(†F
v) ξ
[cf. the notation of Proposition 3.1, (i); Proposition 3.3, (i); Corollary 3.5, (ii);
Corollary 3.6, (ii)]. It follows immediately from the construction of the data
“Gv(MΘ
∗¨) Ψ†FΘ
v ,α” [cf. Example 3.2, (i)] that one has a tautological iso-
morphism of Frobenioids
†CΘ
v
∼ → F†FΘ
v ,α
which is compatible with the associated splittings [cf. the discussion of [IUTchI], Ex-
ample3.2, (v)], andwhichweshallusetoidentifythesetwosplitFrobenioids. Thus,
the isomorphisms of monoids in the bottom line of the third display of Corollary
3.6, (ii), may be interpreted as isomorphisms of split Frobenioids
F†FΘ
v ,α
∼ → Fι
env(MΘ
∗ )∼ → Fξ(MΘ
∗ )∼ → FFξ(†F
v)
[cf. Proposition 3.3, (i); Corollary 3.5, (iii); Corollary 3.6, (iii)] which are compatible
with the subcategories
F2l·ξ(MΘ
∗ ) ⊆ Fξ(MΘ
∗ ); FF2l·ξ(†F
v) ⊆ FFξ(†F
v)
determined by the submonoids “Ψ2l·ξ(−)” [cf. Corollaries 3.5, (ii); 3.6, (ii)] and
which yield isomorphisms of collections of split Frobenioids
F†FΘ
v
∼ → Fenv(MΘ
∗ )∼ → Fgau(MΘ
∗ )∼ → FFgau(†F
v)
[cf. the fourth display of Corollary 3.6, (ii)].
(iii) The direct products in which the submonoids Ψξ(MΘ
∗ ) and ΨFξ(†F
v) are
constructed[cf. theseconddisplayofCorollary3.5,(ii); thefirstdisplayofCorollary
3.6, (ii)] determine natural embeddings of categories [cf. Remark 3.8.1 below]
Fξ(MΘ
∗ ) →
|t|∈Fl
F⊢
cns(MΘ
∗ )|t|; FFξ(†F
v) →
|t|∈Fl
(†C⊢
v )|t|
whichcoincideonthesubcategoriesF2l·ξ(MΘ
∗ ) ⊆ Fξ(MΘ
∗ ),FF2l·ξ(†F
v) ⊆ FFξ(†F
v).
We shall write [cf. Remark 3.8.1 below]
Fgau(MΘ
∗ ) → F⊢
cns(MΘ
∗ )Fl
FFgau(†F
v) → (†C⊢
v )Fl
def
=
|t|∈Fl
def
=
|t|∈Fl
F⊢
cns(MΘ
∗ )|t|
(†C⊢
v )|t|
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 115
for the collections of embeddings of categories obtained by allowing ξ to vary. These
embeddings may be thought of as “Gaussian distributions” and are depicted in
Fig. 3.3 below. In this context, it is useful to observe that we also have natural
diagonal embeddings of categories, i.e., “constant distributions” [cf. Remark
3.8.1 below]
F⊢
cns(MΘ
∗ )∼ → F⊢
cns(MΘ
∗ )⟨Fl ⟩ → F⊢
cns(MΘ
∗ )Fl
F⊢
cns(MΘ
∗ )|t|
†C⊢
v
∼
→ (†C⊢
v )⟨Fl ⟩ → (†C⊢
v )Fl
=
|t|∈Fl
(†C⊢
v )|t|
=
|t|∈Fl
— where the “∼
→ ’s” denote the tautological isomorphisms — cf. the discussion
[and notational conventions!] of [IUTchI], Example 5.4, (i); [IUTchI], Fig. 5.1.
n·
◦
◦
◦...◦
◦...◦...◦
· v
.
.
.
n′
·
◦
◦
◦...◦
◦...◦...◦
· v′
.
.
.
Fig. 3.3: Gaussian distribution
n′′
·
◦
◦
◦...◦
◦...◦...◦
· v′′
Remark 3.8.1. In the present series of papers, we follow the convention [cf.
[IUTchI], §0] that an “isomorphism of categories” is to be understood as an isomor-
phism class of equivalences of categories. On the other hand, in the context of the
discussion of Frobenioids in Definition 3.8, in order to obtain a precise “Frobenioid-
theoretic translation” of the results obtained so far [in the language of monoids] that
involve the phenomenon of conjugate synchronization [cf. Remark 3.5.2; the
discussion of Remark 3.8.3 below], one is obliged to consider the various Frobenioids
indexed by a subscript “|t| ∈ |Fl|” as being determined up to an isomorphism of the
identity functor — i.e., corresponding to an “inner automorphism” in the context
of Corollaries 3.5, (i); 3.6, (i) — which is independent of |t| ∈ |Fl|. In particular,
when there is a danger of confusion, perhaps the simplest approach is to resort to
the original “monoid-theoretic formulations” of Corollaries 3.5, 3.6.
116 SHINICHI MOCHIZUKI
Remark 3.8.2. At this point, it is of interest to pause to discuss the relation-
ship between the theory of the present §3 and the theories of F ±
l -symmetry [cf.
[IUTchI], §6] and Fl -symmetry [cf. [IUTchI], §4, §5] developed in [IUTchI].
(i) First of all, the construction algorithms for the Gaussian monoids dis-
cussed in Corollaries 3.5, (ii); 3.6, (ii), as well as for the closely relating splittings
discussed in Corollaries 3.5, (iii); 3.6, (iii), involve restriction to the decompo-
sition groups of torsion points indexed [via a functorial algorithm] by profinite
conjugacy classes of cusps [cf. Corollary 2.4, (ii)] which are subject to a certain
F ±
l -symmetry [cf. Corollary 2.4, (iii)]. This F ±
l -symmetry may be thought of
as the restriction, to the portion labeled by the valuation v ∈ Vbad under consid-
eration, of the F ±
l -symmetry [cf. [IUTchI], Proposition 6.8, (i)] associated to a
D-Θ±ell-Hodge theater [cf. Remark 2.6.2, (i)]. From the point of view of the issue
of “which portion of the original once-punctured elliptic curve over a number field
XF [cf. [IUTchI], Definition 3.1] is involved”, this theory of split Gaussian monoids
revolves around various labeled [i.e., by elements of copies of Fl or |Fl|] copies of the
local Frobenioids at v of the mono-analyticizations of the F-prime-strips that
appear in a D-Θ±ell-Hodge theater — cf. the various natural embeddings dis-
cussedinDefinition3.8, (iii)—i.e., moreconcretely, copiesoftheportionofthepair
“Gv(Πv) O◃
” determined by a certain submonoid of O◃
. Finally, we recall
Fv
Fv
that after one executes these construction algorithms for split Gaussian monoids
and observes the F ±
l -symmetry discussed above, one may then form holomorphic
or mono-analytic processions, indexed by subsets of |Fl|, as discussed in [IUTchI],
Proposition 6.9, (i), (ii).
(ii) On the other hand, by applying the algorithm of [IUTchI], Proposition 6.7,
one may pass to the local portion at v ∈ Vbad of a D-ΘNF-Hodge theater. At the
level of labels, this amounts to removing the label 0 ∈ |Fl| and identifying this label
with the complement of 0 in |Fl|, i.e., with Fl — cf. the assignment
“ 0, ≻ → > ”
of D-prime-strips discussed in [IUTchI], Proposition 6.7. At the level of local Frobe-
nioids at v ∈ Vbad [i.e., copies of the pair “Πv O◃
”] corresponding to these
Fv
labels, this assignment may be thought of as corresponding to the isomorphisms
of monoids “Ψcns(MΘ
∗ )0
∼
→ Ψcns(MΘ
∗ )⟨Fl ⟩” and “(Ψ†Cv)0
∼
→ (Ψ†Cv)⟨Fl ⟩” dis-
cussed in the first displays of Corollaries 3.5, (iii); 3.6, (iii). This newly obtained
situation involving the local portion at v ∈ Vbad of a D-ΘNF-Hodge theater admits
an Fl -symmetry [cf. [IUTchI], Proposition 4.9, (i)] — cf. the discussion of the
F ±
l -symmetry in the situation of (i). As we shall see in §4 below, at least at the
level of value groups, this newly obtained situation involving Fl -symmetries is
well-suited to relating the theory of the present §3 at v ∈ Vbad to the valuations
∈ Vgood, aswellastotheglobal theory of[IUTchI],§5. Thisglobaltheorysatisfies
the crucial property that it allows one to relate the multiplicative and additive
structures of a global number field [cf. the discussion of [IUTchI], Remark 4.3.2;
[IUTchI], Remark 6.12.5, (ii)]. Finally, starting from this newly obtained situation,
one may proceed to form holomorphic or mono-analytic processions, indexed by
subsets of Fl , as discussed in [IUTchI], Proposition 4.11, (i), (ii), which are com-
patible [cf. [IUTchI], Proposition 6.9, (iii)] with the “|Fl|-processions” discussed in
(i).
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 117
Remark 3.8.3. One central theme of the theory of the present §3 is the ap-
plication of the phenomenon of conjugate synchronization [cf. Remark 3.5.2],
which plays a fundamental role in the theory of the group-theoretic version of
Hodge-Arakelov-theoretic evaluation of the theta function developed in §2. Thus,
it is of interest to pause to discuss precisely what was gained in the present §3 by
applying the conjugate synchronization obtained in §2.
(i) We begin our discussion by reviewing the following direct technical conse-
quences of the conjugate synchronization discussed in Remark 3.5.2:
(a) the isomorphisms of monoids
Ψcns(MΘ
∗ )|t1|
∼
→ Ψcns(MΘ
∗ )|t2|; (Ψ†Cv)|t1|
∼
→ (Ψ†Cv)|t2|; (Ψ†Cv)|t|
∼
→ Ψcns(MΘ
∗ )|t|
— where |t|,|t1|,|t2| ∈ |Fl|; the third isomorphism is well-defined up to
an inner automorphism indeterminacy that is independent of |t| — dis-
cussed in Corollaries 3.5, (i); 3.6, (i);
(b) the construction of well-defined diagonal submonoids
Ψcns(MΘ
∗ )⟨|Fl|⟩ ⊆
|t|∈|Fl|
Ψcns(MΘ
∗ )|t|; Ψcns(MΘ
∗ )⟨Fl ⟩ ⊆
|t|∈Fl
Ψcns(MΘ
∗ )|t|
in Corollary 3.5, (i), and the corresponding diagonal embeddings of cate-
gories — i.e., “constant distributions” — discussed in Definition 3.8, (iii);
(c) the well-defined isomorphisms of monoids
Ψcns(MΘ
∗ )0
∼
→ Ψcns(MΘ
∗ )⟨Fl ⟩; (Ψ†Cv)0
of Corollaries 3.5, (iii); 3.6, (iii);
(d) the restriction to the units of the [composite] isomorphism of monoids
Ψ†FΘ
v ,α
∼
→ ΨFξ(†F
v)
that appears in the third display of Corollary 3.6, (ii) [cf. also Fig. 3.1;
the discussion of Remark 3.6.2, (i)].
Here, we observe that (b) and (c) may be thought of as formal consequences of
(a), while (d) may be thought of as an alternate formulation of the portion of (a)
concerningtheunitsinthecaseof|t| ∈ Fl . Moreover, asdiscussedinRemark3.6.2,
(iii), ultimately, in the present series of papers, we shall be interested in composing
the Θ-link with the composite of the arrows “=⇒”, “⇓”, and “⇐=” of Fig. 3.1 —
i.e., with the isomorphism of monoids that appears in the display of (d). Indeed,
from the point of view of the theory of the present series of papers,
our main application [cf. §4 below] of the conjugate synchronization
discussed in Remark 3.5.2 will consist precisely of the isomorphism of
units of (d), in the context of composition with the Θ-link — cf. the
“coricity of O×” given in [IUTchI], Corollary 3.7, (iii).
∼
→ (Ψ†Cv)⟨Fl ⟩
118 SHINICHI MOCHIZUKI
Finally, in this context, we recall that the isomorphisms of monoids that appear in
the Θ-link or in the third display of Corollary 3.6, (ii), only make sense if one works
with post-anabelian abstract monoids/Frobenioids — i.e., with “Frobenius-like”
structures [cf. the discussion of Remark 3.6.2, (i), (ii)].
(ii) In [IUTchIII], it will be of central importance to consider the theory of
the present paper in the context of the log-wall [i.e., the situation considered in
[AbsTopIII]]. In the context of the log-wall, it will be of fundamental importance to
construct versions of the various Frobenioid-theoretic theta and Gaussian monoids
that appeared in the discussion at the end of (i) that are capable of “penetrating the
log-wall” [cf. the discussion of [AbsTopIII], §I4] — i.e., to construct´ etale-like ver-
sions of these Frobenioid-theoretic theta and Gaussian monoids, by availing oneself
of the right-hand portion of Fig. 3.1. Now to pass from these Frobenioid-theoretic
monoids to their ´ etale-like counterparts, one must apply Kummer theory — cf.
the arrow “=⇒” of Fig. 3.1. Moreover, in order to apply Kummer theory, one
must avail oneself of the cyclotomes contained in [i.e., the torsion subgroups of]
the various groups of units of the relevant monoids. It is at this point that it is
necessary to apply, in the fashion discussed in (i), the conjugate synchroniza-
tion discussed in Remark 3.5.2 in an essential way. That is to say, if one is in a
situation in which one cannot avail oneself of this conjugate synchronization, then
it follows from the distinct, unrelated nature of the basepoints on either side
of the log-wall [cf. the discussion of Remark 3.6.3, (i)] that
onemayonlyconstructdiagonal embeddingsofeithersubmonoidsofGalois-
invariants or sets of Galois-orbits of the various constant monoids [i.e.,
“Ψcns”] involved.
On the other hand, such Galois-invariants or Galois-orbits are clearly insuﬃcient
for conducting Kummer theory [cf. [IUTchIII], Remark 1.5.1, (ii), for a discussion
of a related topic]. Moreover, the operation of passing to sets of Galois-orbits fails
to be compatible with the ring structure — e.g., the additive structure — on [the
formal union with “{0}” of] the various constant monoids. Such an incompatibility
is unacceptable in the context of the theory of the present series of papers since
it is impossible to develop the theory of the log-wall [cf. [AbsTopIII]; [IUTchIII]]
without applying the ring structure within each Hodge theater [cf. the discussion
of Remark 3.6.4, (i)].
(iii) As discussed at the beginning of §1, the problem of giving an explicit
description of what one arithmetic holomorphic structure looks like from the
point of view of a distinct arithmetic holomorphic structure that is only related to
the original arithmetic holomorphic structure via some mono-analytic core is one of
the central themes of the theory of the present series of papers. The phenomenon
of conjugate synchronization as discussed in (i) and (ii) above, as well as the closely
related phenomenon of mono-theta-theoretic cyclotomic rigidity [cf. the discussion
of Remark 3.6.5, (ii)], may be thought of as particular instances of this general
theme. Indeed, from the point of view of classical discussions of scheme-theoretic
arithmetic geometry,
the “natural isomorphisms” that exist between various cyclotomes
that appear in a discussion are typically taken for granted
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 119
— i.e., typically no attention is given to the issue of devising explicit, intrinsic
reconstruction algorithms for these “natural isomorphisms” between cyclotomes.
120 SHINICHI MOCHIZUKI
Section 4: Global Gaussian Frobenioids
In the present §4, we generalize the theory of Gaussian monoids, devel-
oped in §3 in the case of bad v ∈ Vbad, first to the case of nonarchimedean and
archimedean good v ∈ Vgood and then to the global case. One important feature
of these generalizations, especially in the global case, is the theme of compatibility
with the theory of ΘNF- (respectively, Θ±ell
-) Hodge theaters — and, in particu-
lar, the Fl- (respectively, F ±
l-) symmetries of such Hodge theaters — developed
in [IUTchI], §4, §5 (respectively, [IUTchI], §6).
In the following discussion, we assume that we have been given initial Θ-
data as in [IUTchI], Definition 3.1. We begin our discussion by considering good
nonarchimedean v ∈ Vgood Vnon
.
Proposition 4.1. chimedean Primes) Let v ∈ Vgood3.1, (e), (f), write
(Group-theoretic Gaussian Monoids at Good Nonar-
 Vnon. In the notation of [IUTchI], Definition
Πv
def = ΠX
− →v
⊆ Π±
v
def = ΠX
v
⊆ Πcor
v
def = ΠCv
[cf. Definition 2.3, (i), in the case of v ∈ Vbad] — so Π±
v /Πv
discussion preceding [IUTchI], Definition 1.1], Πcor
v /Π±
∼
= F ±
v
l ;
Πv Gv(Πv), Π±
v Gv(Π±
v ), Πcor
v Gv(Πcor
v )
∼
= Z/lZ [cf. the
for the quotients — which admit natural isomorphisms Gv(Πv)∼
→ Gv(Π±
v )∼
→
Gv(Πcor
v )∼
→ Gv — determined by the natural surjections to Gv; Δv, Δ±
v , Δcor
v for
the respective kernels of these quotients. Also, we recall that Π±
v , Πcor
v , Gv(Πv),
Gv(Π±
v ), and Gv(Πcor
v ) may be reconstructed algorithmically [cf. [IUTchI],
Corollary 1.2, and its proof; [AbsAnab], Lemma 1.3.8] from the topological group
Πv.
(i) (Constant Monoids) The functorial group-theoretic algorithm of [Ab-
sTopIII], Corollary 1.10, (b) [cf. also the discussion of Remark 1.11.5, (i), in
the case of v ∈ Vbad; the discussion of “Mv(−)” in [IUTchI], Definition 5.2, (v)]
yields a functorial group-theoretic algorithm in the topological group Gv for
constructing the ind-topological submonoid [which is naturally isomorphic to
O◃
]
Fv
Ψcns(Gv) ⊆ lim
− →
H1(J,μZ(Gv))
J
— where J ranges over the open subgroups of Gv; μZ(Gv) is as in [AbsTopIII],
Corollary 1.10, (b) — equipped with its natural Gv-action. In particular, we obtain
a functorial group-theoretic algorithm in the topological group Πv for constructing
the ind-topological submonoid
Ψcns(Πv) def = Ψcns(Gv(Πv)) ⊆ lim
− →
J
⊆ lim
− →
J
H1(Π±
v |J,μZ(Gv(Πv))) ⊆ lim
− →
J
H1(Gv(Πv)|J,μZ(Gv(Πv)))
H1(Πv|J,μZ(Gv(Πv)))
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 121
— where J ranges over the open subgroups of Gv(Πv) — equipped with its natural
Gv(Πv)-action [cf. Proposition 3.1, (ii), in the case of v ∈ Vbad].
(ii) (Mono-analytic Semi-simplifications) The functorial algorithm dis-
cussed in [IUTchI], Example 3.5, (iii), for constructing “(R⊢
≥0)v” [cf. also [Ab-
sTopIII], Proposition 5.8, (iii)] yields a functorial group-theoretic algorithm
in the topological group Gv for constructing a topological monoid R≥0(Gv) equipped
with a natural isomorphism
ΨR
cns(Gv) def = (Ψcns(Gv)/Ψcns(Gv)×)rlf∼
→ R≥0(Gv)
— where the superscript “×” denotes the submonoid of units; the superscript “rlf”
denotes the realification [which is isomorphic to R≥0] of the monoid in parentheses
[which is isomorphic to Q≥0] — and a distinguished element
logGv(pv) ∈ R≥0(Gv)
— i.e., the element “logD
Φ(pv)” of [IUTchI], Example 3.5, (iii). Write
Ψss
cns(Gv) def = Ψcns(Gv)× ×R≥0(Gv)
— which we shall think of as a sort of “semi-simplified version” of Ψcns(Gv).
Also, just as in (i), we shall abbreviate notation that denotes a dependence on
“Gv(Πv)” [e.g., a “Gv(Πv)” in parentheses] by means of notation that denotes a
dependence on “Πv”.
(iii) (Labels, F ±
l -Symmetries, and Conjugate Synchronization) Let
t ∈ LabCusp±(Πv) def = LabCusp±(B(Πv)0) [cf. [IUTchI], Definition 6.1, (iii)]. In
the following, we shall use analogous conventions to the conventions introduced in
Corollary 3.5 concerning subscripted labels. Then if we think of the cuspidal
inertia groups ⊆ Πv corresponding to t as subgroups of cuspidal inertia groups
of Π±
v [cf. Remark 2.3.1, in the case of v ∈ Vbad], then the Δ±
v -outer action of
F ±
∼
= Δcor
l
v /Δ±
v on Π±
v [cf. Corollary 2.4, (iii), in the case of v ∈ Vbad] induces
isomorphisms between the pairs
Gv(Πv)t Ψcns(Πv)t
— consisting of a labeled ind-topological monoid equipped with the action of a
labeled topological group — for distinct t ∈ LabCusp±(Πv). We shall refer to
these isomorphisms as [F ±
l -]symmetrizing isomorphisms [cf. Remark 3.5.2,
in the case of v ∈ Vbad]. These symmetrizing isomorphisms determine diagonal
submonoids
Ψcns(Πv)⟨|Fl|⟩ ⊆
Ψcns(Πv)|t|; Ψcns(Πv)⟨Fl ⟩ ⊆
|t|∈|Fl|
|t|∈Fl
of the respective product monoids compatible with the respective actions by sub-
scripted versions of Gv(Πv) [cf. the discussion of Corollary 3.5, (i), in the case of
v ∈ Vbad], as well as an isomorphism of ind-topological monoids
Ψcns(Πv)0
∼
→ Ψcns(Πv)⟨Fl ⟩
Ψcns(Πv)|t|
122 SHINICHI MOCHIZUKI
compatible with the respective actions by subscripted versions of Gv(Πv) [cf. Corol-
lary 3.5, (iii), in the case of v ∈ Vbad].
(iv) (Theta and Gaussian Monoids) Relative to the notational conventions
discussed at the end of (ii), let us write
Ψenv(Πv) def = Ψcns(Πv)× × R≥0·logΠv(pv)·logΠv(Θ)
— where the notation “logΠv(pv)·logΠv(Θ)” is to be understood as a formal sym-
bol [cf. the discussion of [IUTchI], Example 3.3, (ii)] — and
Ψgau(Πv) def = Ψcns(Πv)×
⟨Fl ⟩ × R≥0· ...,j2
⊆
Ψss
cns(Πv)j=
j∈Fl
j∈Fl
·logΠv(pv),...
Ψcns(Πv)×
j × R≥0(Πv)j
— where, by abuse of notation, we also write “j” for the natural number ∈ {1,...,l }
determined by an element j ∈ Fl . In particular, [cf. (i), (ii), (iii)] we obtain a
functorial group-theoretic algorithm in the topological group Πv for construct-
ing the theta monoid Ψenv(Πv) and the Gaussian monoid Ψgau(Πv), equipped
with their [evident] natural Gv(Πv)-actions and splittings, as well as the formal
evaluation isomorphism [cf. Corollary 3.5, (ii), in the case of v ∈ Vbad]
Ψenv(Πv)∼
→ Ψgau(Πv)
logΠv(pv)·logΠv(Θ) → ...,j2
·logΠv(pv),...
— which restricts to the identity on the respective copies of “Ψcns(Πv)×” and is
compatible with the respective natural actions of Gv(Πv) as well as with the nat-
ural splittings on the domain and codomain.
Proof. The various assertions of Proposition 4.1 follow immediately from the
definitions and the references quoted in the statements of these assertions. ⃝
Remark 4.1.1.
(i) Proposition 4.1 may be thought of as a sort of “easy” formal general-
ization of much of the theory of §2, §3 — more precisely, the portion constituted
by Proposition 3.1 and Corollaries 2.4, 3.5 — to the case of v ∈ Vgood Vnon. By
comparison to the corresponding portion of the theory of §2, §3, this generalization
is somewhat tautological and, for the most part, “vacuous”. As we shall see later,
the reason for considering this formal generalization to v ∈ Vgood Vnon is that it
allows one to “globalize” the theory of §2, §3, i.e., by gluing together the theories
at v ∈ Vbad and v ∈ Vgood
.
(ii) The symmetrizing isomorphisms of Proposition 4.1, (iii), constitute the
analogue at v ∈ Vgood Vnon of the conjugate synchronization at v ∈ Vbad
discussed in Corollary 3.5, (i); Remark 3.5.2. In this context, it is perhaps most
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 123
natural to think of the “copies of Gv(Πv) labeled by t ∈ LabCusp±(Πv)” as the
quotients
Dt/It
— where It is a cuspidal inertia group ⊆ Πv corresponding to t; Dt is the
corresponding decomposition group ⊆ Πv [i.e., the normalizer, or, equivalently,
the commensurator, of It in Πv — cf., e.g., [AbsSect], Theorem 1.3, (ii)]; we think
of Dt/It as being equipped with the isomorphism Dt/It
∼
→ Gv(Πv) induced by the
natural surjection Πv Gv(Πv).
(iii) One may also formulate an easy tautological formal analogue at v ∈
Vgood Vnon of the multiradiality and uniradiality assertions of Proposition 3.4,
Corollary 3.7 at v ∈ V. For instance,
(a) the construction of the monoids Ψcns(Πv) [cf. Proposition 4.1, (i)] is
uniradial [cf. Proposition 3.4, (ii)], while
(b) the construction of the monoids Ψss
cns(Πv), Ψenv(Πv), and Ψgau(Πv) [cf.
Proposition4.1,(ii),(iv)],aswellasoftheisomorphismΨenv(Πv)∼
→Ψgau(Πv)
[cf. Proposition 4.1, (iv)], is multiradial.
We leave the routine details to the reader. Ultimately, in the present series of
papers [cf., especially, the theory of [IUTchIII]], we shall be interested in a global
analogue of the theory of multiradiality and uniradiality developed in §1, §3 at
v ∈ Vbad. This global analogue will “specialize” to the theory of §1, §3 at v ∈ Vbad
and to the formal analogue just discussed [i.e., (a), (b)] at v ∈ Vgood Vnon
.
Proposition 4.2. (Frobenioid-theoretic Gaussian Monoids at Good
Nonarchimedean Primes) We continue to use the notation of Proposition 4.1.
Let †F
be a pv-adic Frobenioid that appears in a Θ-Hodge theater †HT Θ
=
v
({†F
w}w∈V,
†Fmod) [cf. [IUTchI], Definition 3.6] — cf., for instance, the Frobe-
nioid “F
= Cv” of [IUTchI], Example 3.3, (i); here, we assume [for simplicity] that
v
the base category of †F
v is equal to Btemp(†Πv)0, and we denote by means of a “†”
the various topological groups associated to †Πv that correspond to the topological
groups associated to Πv in Proposition 4.1. Write
Gv(†Πv) Ψ†F
v
for the ind-topological monoid Ψ†F
equipped with a continuous Gv(†Πv)-action
v
determined, up to inner automorphism [i.e., up to an automorphism arising
from an element of †Πv], by †F
v [cf. the construction of “ΨCv” in Example 3.2,
(ii), in the case of v ∈ Vbad; the discussion of “‡Mv” in [IUTchI], Definition 5.2,
(vi); the discussion of [AbsTopIII], Remark 3.1.1] and
†Gv Ψ†F⊢
v
for the ind-topological monoid Ψ†F⊢
v equipped with a continuous †Gv-action deter-
mined, up to inner automorphism [i.e., up to an automorphism arising from an
124 SHINICHI MOCHIZUKI
element of †Gv], by the portion indexed by v of the F⊢-prime-strip {†F⊢
w}w∈V
determined by the Θ-Hodge theater †HT Θ [cf. [IUTchI], Definition 3.6; [IUTchI],
Definition 5.2, (ii)].
(i) (Constant Monoids) There exists a unique Gv(†Πv)-equivariant iso-
morphism of monoids [cf. Proposition 3.3, (ii), in the case of v ∈ Vbad; the
discussion of “‡Mv” in [IUTchI], Definition 5.2, (vi)]
Ψ†F
∼
→ Ψcns(†Πv)
v
— cf. Remark 1.11.1, (i), (a); [AbsTopIII], Proposition 3.2, (iv).
(ii) (Mono-analytic Semi-simplifications) There exists a unique †Gv-
equivariant Z×-orbit of isomorphisms of topological groups
Ψ×
†F⊢
v
∼
→ Ψcns(†Gv)×
— cf. Remark 1.11.1, (i), (b); [AbsTopIII], Proposition 3.3, (ii) — as well as a
unique isomorphism of monoids
ΨR
†F⊢
v
def = (Ψ†F⊢
v /Ψ×
†F⊢
v
)rlf∼
→ ΨR
cns(†Gv)
that maps the distinguished element of ΨR
†F⊢
determined by the unique gen-
v
erator of Ψ†F⊢
v /Ψ×
†F⊢
to the distinguished element of ΨR
cns(†Gv) determined by
v
log†Gv(pv) ∈ R≥0(†Gv) [cf. Proposition 4.1, (ii)]. In particular, one may define
a “semi-simplified version” Ψss
def = Ψ×
×ΨR
†F⊢
†F⊢
†F⊢
of Ψ†F⊢
v ; the isomorphisms
v
v
v
discussed above determine a natural poly-isomorphism of ind-topological monoids
Ψss
†F⊢
v
∼
→ Ψss
cns(†Gv)
[cf. Proposition 4.1, (ii)] that is compatible with the natural splittings on the domain
and codomain. Write Ψss
def = Ψss
†F
†F⊢
; thus, it follows from the definitions [cf. also
v
v
the unique isomorphism of (i)] that we have a natural isomorphism [i.e., as opposed
to a poly-isomorphism!] Ψss
∼
→ Ψss
†F
†F⊢
v
.
v
(iii) (Labels, F ±
l -Symmetries, and Conjugate Synchronization) The
isomorphism of (i) determines, for each t ∈ LabCusp±(†Πv), a collection of com-
patible isomorphisms
(Ψ†F
)t
∼
→ Ψcns(†Πv)t
v
— which are well-defined up to composition with an inner automorphism of
†Πv which is independent of t ∈ LabCusp±(†Πv) [cf. Corollary 3.6, (i), in the
case of v ∈ Vbad] — as well as [F ±
l -]symmetrizing isomorphisms, induced by
v
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 125
the †Δ±
v -outer action of F ±
∼
= †Δcor
l
v /†Δ±
v on †Π±
v [cf. Corollary 2.4, (iii), in
the case of v ∈ Vbad], between the data indexed by distinct t ∈ LabCusp±(†Πv).
Moreover, these symmetrizing isomorphisms determine [various diagonal sub-
monoids, as well as] an isomorphism of ind-topological monoids
(Ψ†F
)0
∼
→ (Ψ†F
v
)⟨Fl ⟩
compatible with the respective actions by subscripted versions of Gv(†Πv) [cf. Corol-
lary 3.6, (iii), in the case of v ∈ Vbad].
(iv) (Theta and Gaussian Monoids) Write
Ψ†FΘ
v , ΨFgau(†F
v)
for the monoids equipped with Gv(†Πv)-actions and natural splittings deter-
mined, respectively — via the isomorphisms of (i), (ii), and (iii) — by the monoids
Ψenv(†Πv), Ψgau(†Πv), Galois actions, and splittings of Proposition 4.1, (iv). Then
the definition of the various monoids involved, together with the formal evaluation
isomorphism of Proposition 4.1, (iv), gives rise to a collection of natural isomor-
phisms [cf. Corollary 3.6, (ii), in the case of v ∈ Vbad]
Ψ†FΘ
v
∼
→ Ψenv(†Πv)∼
→ Ψgau(†Πv)∼
→ ΨFgau(†F
v)
— which restrict to the identity or to the [restriction to “(−)×” of the] isomor-
phism of (i) [or its inverse] on the various copies of Ψ×
†F
, “Ψcns(†Πv)×” and are
v
compatible with the various natural actions of Gv(†Πv) and natural splittings.
Proof. The various assertions of Proposition 4.2 follow immediately from the
definitions and the references quoted in the statements of these assertions. ⃝
Remark 4.2.1.
(i) In the case of v ∈ Vbad treated in §3, we did not discuss an analogue of the
“mono-analytic semi-simplification” Ψss
cns(†Gv)of Proposition 4.1, (ii). On the
other hand, one verifies immediately that one may define, in the case of v ∈ Vbad
— via the same group-theoretic algorithms as those applied in Proposition 4.1, (i),
(ii) — ind-topological monoids Ψss
cns(†Gv), R≥0(†Gv) equipped with natural †Gv-
actions, a natural isomorphism [i.e., as in the first display of Proposition 4.1, (ii)],
a distinguished element log†Gv(pv) ∈ R≥0(†Gv), and a tautological splitting
Ψss
cns(†Gv) = Ψss
cns(†Gv)× × R≥0(†Gv)
[cf. Proposition 4.1, (ii)]. Moreover, if we write
Ψcns(Πv) def = Ψcns(MΘ
∗ (Πv))
— cf. the various monoids “∞Ψ(−)” that appeared in the discussion of §3.
(iii) In the situation of (ii), if one regards the pairs Gv(Πv) Ψenv(Πv),
126 SHINICHI MOCHIZUKI
— where the latter “Ψcns(−)” is as in Proposition 3.1, (ii) — then, by applying
the cyclotomic rigidity isomorphisms of Definition 1.1, (ii), and the discussion at
the beginning of Corollary 2.9, one obtains a functorial group-theoretic [i.e., in the
topological group Πv] Πv-equivariant isomorphism
Ψcns(Πv)× ∼
→ Ψss
cns(Gv(Πv))×
— cf. the discussion of “Ψss
cns(−)” in the case of v ∈ Vgood Vnon in Proposition
4.1, (ii). Finally, we observe that, relative to the above notation, one has analogues
of “Ψss
†F⊢
” and of Proposition 4.2, (i), (ii), in the case of v ∈ Vbad. We leave the
v
routine details to the reader.
(ii) Note that in the case of v ∈ Vgood Vnon, the monoids Ψenv(Πv), Ψgau(Πv)
of Proposition 4.1, (iv), are already divisible. Thus, it is natural, in the case of
v ∈ Vgood Vnon, to simply set
∞Ψenv(Πv) def = Ψenv(Πv);∞Ψgau(Πv) def = Ψgau(Πv)
∞Ψ†FΘ
v
def = Ψ†FΘ
v ; ∞ΨFgau(†F
v) def = ΨFgau(†F
v)
Gv(Πv) Ψgau(Πv), Gv(Πv)∞Ψenv(Πv), Gv(Πv)∞Ψgau(Πv) up to an
indeterminacy with respect to Πv-inner automorphisms, then one obtains data
which we shall denote by means of the notation
Ψenv(Btemp(Πv)0), Ψgau(Btemp(Πv)0), ∞Ψenv(Btemp(Πv)0), ∞Ψgau(Btemp(Πv)0)
— i.e., since Πv may only be reconstructed from Btemp(Πv)0 up to an inner auto-
morphism indeterminacy [cf. the discussion of [IUTchI], §0].
(iv) Suppose that v ∈ Vbad. Then the above discussion motivates the following
notational conventions. First, let us write
Ψenv(Πv) def = Ψenv(MΘ
∗ (Πv)), Ψgau(Πv) def = Ψgau(MΘ
∗ (Πv))
∞Ψenv(Πv) def
= ∞Ψenv(MΘ
∗ (Πv)), ∞Ψgau(Πv) def
= ∞Ψgau(MΘ
∗ (Πv))
— cf. (ii) above; the notation of Corollary 3.5, (ii). When these monoids equipped
with various topological group actions are considered only up to a Πv-inner au-
tomorphism indeterminacy, we shall denote the resulting data by means of the
notation
Ψenv(Btemp(Πv)0), Ψgau(Btemp(Πv)0), ∞Ψenv(Btemp(Πv)0), ∞Ψgau(Btemp(Πv)0)
— cf. (iii) above.
Next, we consider [good] archimedean v ∈ Varc (⊆ Vgood).
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 127
Proposition 4.3. (Aut-holomorphic-space-theoretic Gaussian Monoids
at Archimedean Primes) Let v ∈ Varc (⊆ Vgood). Recall the Aut-holomorphic
orbispaces of [IUTchI], Example 3.4, (i),
Uv
def
= X
− →v
→ U±
v
def
= Xv → Ucor
v
def
= Cv
— so Gal(Uv/U±
v )∼
= Z/lZ [cf. the discussion preceding [IUTchI], Definition 1.1],
Gal(U±
v /Ucor
v )∼
= F ±
l ; we shall apply the notation “A ”, “A ” of [IUTchI], Ex-
ample 3.4, (i), to these Aut-holomorphic orbispaces. Also, we shall write A◃ ⊆
A ⊆ A for the topological monoid of nonzero elements of absolute value ≤ 1 of
the complex archimedean field A [cf. the slightly diﬀerent notation of [AbsTopIII],
Corollary 4.5, (ii)]. Finally, we recall the object D⊢
v of the category “TM⊢” of split
topological monoids discussed in [IUTchI], Example 3.4, (ii); we shall write D⊢
v(Uv)
when we wish to regard D⊢
v as an object algorithmically constructed from Uv.
(i) (Constant Monoids) There is a functorial algorithm in the Aut-
holomorphic space Uv for constructing the topological monoid
Ψcns(Uv) def
= A◃
Uv
— cf. [IUTchI], Example 3.4, (i); the discussion of “Mv(−)” in [IUTchI], Defi-
nition 5.2, (vii); [AbsTopIII], Definition 4.1, (i); [AbsTopIII], Corollary 2.7, (e).
Moreover, if we write Ψcns(D⊢
v) for the underlying topological monoid of D⊢
v, then
we have a tautological isomorphism of topological monoids
Ψcns(Uv)∼
→ Ψcns(D⊢
v(Uv))
[cf. [IUTchI], Example 3.4, (ii)] — which we shall use to identify these two
topological monoids.
(ii) (Mono-analytic Semi-simplifications) The functorial algorithm dis-
cussed in [IUTchI], Example 3.5, (iii), for constructing “(R⊢
≥0)v” [cf. also [Ab-
sTopIII], Proposition 5.8, (vi)] yields a functorial algorithm in the object D⊢
v
of TM⊢ for constructing a topological monoid R≥0(D⊢
v) equipped with a distin-
guished element
logD⊢
v (pv) ∈ R≥0(D⊢
v)
— i.e., the element “logD
Φ(pv)” of [IUTchI], Example 3.5, (iii). Write
Ψss
cns(D⊢
v) def = Ψcns(D⊢
v)× ×R≥0(D⊢
v)
— where the superscript “×” denotes the submonoid of units — which we shall
think of as a sort of “semi-simplified version” of Ψcns(D⊢
v). We shall abbreviate
notation that denotes a dependence on “D⊢
v(Uv)” [e.g., a “D⊢
v(Uv)” in parenthe-
ses] by means of notation that denotes a dependence on “Uv”. Finally, there is a
functorial algorithm in the Aut-holomorphic space Uv for constructing the natural
isomorphism [which arises immediately from the definitions]
ΨR
cns(Uv) def = Ψcns(Uv)/Ψcns(Uv)× ∼
→ R≥0(Uv)
Ψcns(Uv)|t|
128 SHINICHI MOCHIZUKI
— cf. [IUTchI], Example 3.4, (i).
(iii) (Labels, F ±
l -Symmetries, and Conjugate Synchronization) Let
t ∈ LabCusp±(Uv) [cf. [IUTchI], Definition 6.1, (iii)]. In the following, we shall
use analogous conventions to the conventions introduced in Corollary 3.5 concern-
ing subscripted labels. Then the action of F ±
∼
l
= Gal(U±
v /Ucor
v ) on the var-
ious Gal(Uv/U±
v )-orbits of cusps of Uv [cf. the definition of “LabCusp±(−)” in
[IUTchI], Definition 6.1, (iii)] induces isomorphisms between the labeled topo-
logical monoids
Ψcns(Uv)t
for distinct t ∈ LabCusp±(Uv). We shall refer to these isomorphisms as [F ±
l-
]symmetrizing isomorphisms [cf. Remark 3.5.2, in the case of v ∈ Vbad]. These
symmetrizing isomorphisms determine diagonal submonoids
Ψcns(Uv)⟨|Fl|⟩ ⊆
Ψcns(Uv)|t|; Ψcns(Uv)⟨Fl ⟩ ⊆
|t|∈|Fl|
|t|∈Fl
of the respective product monoids [cf. the discussion of Corollary 3.5, (i), in the
case of v ∈ Vbad], as well as an isomorphism of topological monoids
Ψcns(Uv)0
∼
→ Ψcns(Uv)⟨Fl ⟩
[cf. Corollary 3.5, (iii), in the case of v ∈ Vbad].
(iv) (Theta and Gaussian Monoids) Relative to the notational conventions
discussed in (ii), let us write
Ψenv(Uv) def = Ψcns(Uv)× × R≥0·logUv(pv)·logUv(Θ)
— where the notation “logUv(pv)·logUv(Θ)” is to be understood as a formal symbol
[cf. the discussion of [IUTchI], Example 3.4, (iii)] — and
Ψgau(Uv) def = Ψcns(Uv)×
⟨Fl ⟩ × R≥0· ...,j2
⊆
Ψss
cns(Uv)j=
j∈Fl
j∈Fl
·logUv(pv),...
Ψcns(Uv)×
j ×R≥0(Uv)j
— where, by abuse of notation, we also write “j” for the natural number ∈ {1,...,l }
determined by an element j ∈ Fl . In particular, [cf. (i), (ii), (iii)] we obtain a
functorial algorithm in the Aut-holomorphic space Uv for constructing the theta
monoid Ψenv(Uv) and the Gaussian monoid Ψgau(Uv), equipped with their [ev-
ident] natural splittings, as well as the formal evaluation isomorphism [cf.
Corollary 3.5, (ii), in the case of v ∈ Vbad]
Ψenv(Uv)∼
→ Ψgau(Uv)
logUv(pv)·logUv(Θ) → ...,j2
·logUv(pv),...
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 129
— which restricts to the identity on the respective copies of “Ψcns(Uv)×” and is
compatible with the natural splittings on the domain and codomain.
Proof. The various assertions of Proposition 4.3 follow immediately from the
definitions and the references quoted in the statements of these assertions. ⃝
Remark 4.3.1. Analogous observations to the observations made in Remark
4.1.1, (i), (ii), (iii), may be made in the present case of v ∈ Varc. We leave the rou-
tine details to the reader. In this context, we note that the cuspidal decomposition
groups that appear in the discussion of Remark 4.1.1, (ii), may be thought of as
corresponding to the “Ap” that appear in [AbsTopIII], Corollary 2.7, (e) — i.e., in
the construction of AUv — in the case of points p that belong to “suﬃciently small”
neighborhoods of the cusps that correspond to an element t ∈ LabCusp±(Uv).
Proposition 4.4. (Frobenioid-theoretic Gaussian Monoids at Archime-
dean Primes) We continue to use the notation of Proposition 4.3. Let †F
=
v
(†Cv,
†Dv,
†κv) be the collection of data indexed by v ∈ Varc of a Θ-Hodge theater
†HT Θ = ({†F
w}w∈V,
†Fmod) [cf. [IUTchI], Definition 3.6; [IUTchI], Example
3.4, (i)]. Write †F⊢
v = (†C⊢
†D⊢
†τ⊢
v ,
v,
v ) for the data indexed by v [cf. the discussion
of [IUTchI], Example 3.4, (ii)] of the F⊢-prime-strip determined by the Θ-Hodge
theater †HT Θ [cf. [IUTchI], Definition 3.6; [IUTchI], Definition 5.2, (ii)]. Also, let
us write †Uv
def
= †Dv and †U±
†Ucor
v ,
v for the Aut-holomorphic orbispaces associated
to †Uv that correspond to “U±
v ”, “Ucor
v ”, respectively [cf. the discussion of [IUTchI],
Definition 6.1, (ii)].
(i) (Constant Monoids) In the notation of [IUTchI], Definition 3.6; [IUTchI],
Example 3.4, (i) [cf. also the discussion of “‡Mv” in [IUTchI], Definition 5.2,
(viii)], the Kummer structure
†κv : Ψ†F
def
= O◃(†Cv) → A†Dv
v
on the category †Cv, together with the tautological equality †Dv = †Uv of Aut-
holomorphic spaces, determine a unique isomorphism
Ψ†F
∼
→ Ψcns(†Uv)
v
of topological monoids.
(ii) (Mono-analytic Semi-simplifications) Write Ψ†F⊢
def
= O◃(†C⊢
v ) [cf.
v
[IUTchI], Example 3.4, (ii)]. Then there exists a unique {±1}-orbit of isomor-
phisms of topological groups
Ψ×
†F⊢
v
∼
→ Ψcns(†D⊢
v)×
as well as a unique isomorphism of monoids
ΨR
†F⊢
v
def = Ψ†F⊢
v /Ψ×
†F⊢
v
∼
→ ΨR
cns(†D⊢
v) def
= R≥0(†D⊢
v)
130 SHINICHI MOCHIZUKI
that maps the distinguished element of ΨR
†F⊢
determined by pv = e = 2.71828...
v
[i.e., the element of the complex archimedean field that gives rise to Ψ†F
whose nat-
v
ural logarithm is equal to 1] to the distinguished element of ΨR
cns(†D⊢
v) determined by
†D⊢
log
v (pv) ∈ R≥0(†D⊢
v) [cf. the first display of Proposition 4.3, (ii)]. In particular,
if we write Ψss
def = Ψ×
× ΨR
†F⊢
†F⊢
†F⊢
for the “semi-simplified version” of Ψ†F⊢
v ,
v
v
v
then the former distinguished element, together with the poly-isomorphism of the
first display of the present (ii), determine a natural poly-isomorphism of topological
monoids
Ψss
†F⊢
v
∼
→ Ψss
cns(†D⊢
v)
[cf. Proposition 4.3, (ii)] that is compatible with the natural splittings on the domain
and codomain. Write Ψss
def = Ψss
†F
†F⊢
; thus, it follows from the definitions that we
v
v
∼
have a natural isomorphism Ψss
†F
→ Ψss
†F⊢
.
v
(iii) (Labels, F ±
l -Symmetries, and Conjugate Synchronization) The
isomorphism of (i) determines, for each t ∈ LabCusp±(†Uv), a collection of com-
patible isomorphisms
v
(Ψ†F
)t
∼
→ Ψcns(†Uv)t
v
[cf. Corollary 3.6, (i), in the case of v ∈ Vbad], as well as [F ±
l -]symmetrizing
isomorphisms, induced by the action of F ±
∼
l
= Gal(†U±
v /†Ucor
v ) on the vari-
ous Gal(†Uv/†U±
v )-orbits of cusps of †Uv [cf. the definition of “LabCusp±(−)” in
[IUTchI], Definition 6.1, (iii)], between the data indexed by distinct t ∈ LabCusp±(†Uv).
Moreover, these symmetrizing isomorphisms determine [various diagonal sub-
monoids, as well as] an isomorphism of topological monoids
(Ψ†F
)0
∼
→ (Ψ†F
v
)⟨Fl ⟩
v
[cf. Corollary 3.6, (iii), in the case of v ∈ Vbad].
(iv) (Theta and Gaussian Monoids) Write
Ψ†FΘ
v , ΨFgau(†F
v)
for the topological monoids equipped with natural splittings determined, respec-
tively — via the isomorphisms of (i), (ii), and (iii) — by the monoids Ψenv(†Uv),
Ψgau(†Uv) and splittings of Proposition 4.3, (iv). Then the definition of the various
monoids involved, together with the formal evaluation isomorphism of Proposition
4.3, (iv), gives rise to a collection of natural isomorphisms [cf. Corollary 3.6,
(ii), in the case of v ∈ Vbad]
Ψ†FΘ
v
∼
→ Ψenv(†Uv)∼
→ Ψgau(†Uv)∼
→ ΨFgau(†F
v)
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 131
— which restrict to the identity or to the [restriction to “(−)×” of the] isomor-
phism of (i) [or its inverse] on the various copies of Ψ×
†F
, “Ψcns(†Uv)×” and are
v
compatible with the various natural splittings.
Proof. The various assertions of Proposition 4.4 follow immediately from the
definitions and the references quoted in the statements of these assertions. ⃝
Remark 4.4.1. In the case of v ∈ Varc, one verifies immediately that one can
make a remark analogous to Remark 4.2.1, (ii).
Corollary 4.5. Hodge Theaters) Let
(Group-theoretic Monoids Associated to Base-Θ±ell
-
†HT D-Θ±ell = (†D≻
†φΘ±
±
←− †DT
†φΘell
±
−→ †D ±)
be a D-Θ±ell-Hodge theater [relative to the given initial Θ-data — cf. [IUTchI],
Definition 6.4, (iii)] and
‡D= {‡Dv}v∈V
a D-prime-strip; here, we assume [for simplicity] that ‡Dv = Btemp(‡Πv)0 for v ∈
Vnon. Also, we shall denote the D⊢-prime-strip associated to — i.e., the mono-
analyticization of — a D-prime-strip [cf. [IUTchI], Definition 4.1, (iv)] by means of
a superscript “⊢” and assume [for simplicity] that ‡D⊢
v
= Btemp(‡Gv)0 for v ∈ Vnon
.
(i) (Constant Monoids) There is a functorial algorithm in the D-prime-
strip ‡D for constructing the assignment Ψcns(‡D) given by
Vnon ∋ v → Ψcns(‡D)v
Varc ∋ v → Ψcns(‡D)v
def
= Gv(‡Πv) Ψcns(‡Πv)
def = Ψcns(‡Dv)
— where the data in brackets “{−}” is to be regarded as being well-defined only up
to a ‡Πv-conjugacy indeterminacy — cf. Remark 4.2.1, (i), and Propositions
3.1, (ii); 4.1, (i); 4.3, (i).
(ii) (Mono-analytic Semi-simplifications) There is a functorial algo-
rithm in the D⊢-prime-strip ‡D⊢ for constructing the assignment Ψss
cns(‡D⊢) given
by
Vnon ∋ v → Ψss
cns(‡D⊢)v
Varc ∋ v → Ψss
cns(‡D⊢)v
def
= ‡Gv Ψss
cns(‡Gv)
def = Ψss
cns(‡D⊢
v)
— where the data in brackets “{−}” is to be regarded as being well-defined only up to
a ‡Gv-conjugacy indeterminacy; each “Ψss
cns(−)” is equipped with a splitting,
i.e., a direct product decomposition
Ψss
cns(‡D⊢)v = Ψss
cns(‡D⊢)×
v × R≥0(‡D⊢)v
132 SHINICHI MOCHIZUKI
as the product of the submonoid of units and a submonoid with no nontrivial units
[each of which is equipped with the action of a topological group when v ∈ Vnon];
each submonoid R≥0(‡D⊢)v is equipped with a distinguished element
log‡D⊢(pv) ∈ R≥0(‡D⊢)v
— cf. Remark 4.2.1, (i); Propositions 4.1, (ii), and 4.3, (ii). Here, if we regard ‡D⊢
as an object functorially constructed from ‡D, then there is a functorial algorithm
in the D-prime-strip ‡D for constructing isomorphisms [of ind-topological abelian
groups, equipped with the action of a topological group when v ∈ Vnon]
Ψcns(‡D)×
v
∼
→ Ψss
cns(‡D⊢)×
v
for each v ∈ V — cf. Remark 4.2.1, (i); Propositions 4.1, (i), (ii), and 4.3,
(i), (ii). Finally, there is a functorial algorithm in the D⊢-prime-strip ‡D⊢ for
constructing a Frobenioid
D (‡D⊢)
[cf. the Frobenioid “Dmod” of [IUTchI], Example 3.5, (iii)] isomorphic to the Frobe-
nioid “Cmod” of [IUTchI], Example 3.5, (i), equipped with a bijection
Prime(D (‡D⊢))∼
→ V
— where we write “Prime(−)” for the set of primes associated to the divisor
monoid of the Frobenioid in parentheses [cf. the discussion of [IUTchI], Exam-
ple 3.5, (i)] — and, for each v ∈ V, an isomorphism of topological monoids
‡ρD ,v : ΦD (‡D⊢),v
∼
→ R≥0(‡D⊢)v, where we write “ΦD (‡D⊢),v” for the submonoid
[isomorphic to R≥0] of the divisor monoid of D (‡D⊢) associated to v [cf. the iso-
morphism “ρD
v ” of [IUTchI], Example 3.5, (iii)].
(iii) (Labels, F ±
l -Symmetries, and Conjugate Synchronization) Write
†ζ≻ : LabCusp±(†D≻)∼
→ T
for the bijection †ζ± ◦ †ζΘell
0 ◦ (†ζΘ±
0 )−1 arising from the bijections discussed in
[IUTchI], Proposition 6.5, (i), (ii), (iii). Let t ∈ LabCusp±(†D≻). In the following,
we shall use analogous conventions to the conventions introduced in Corollary 3.5
concerning subscripted labels. Then the various local F ±
l -actions discussed
in Corollary 3.5, (i), and Propositions 4.1, (iii); 4.3, (iii), induce isomorphisms
between the labeled data
Ψcns(†D≻)t
[cf. (i)] for distinct t ∈ LabCusp±(†D≻). We shall refer to these isomorphisms
as [F ±
l -]symmetrizing isomorphisms. These symmetrizing isomorphisms are
compatible, relative to †ζ≻, with the F ±
l -symmetry of the associated D-Θell
-
bridge [cf. [IUTchI], Proposition 6.8, (i)] and determine diagonal submonoids
Ψcns(†D≻)⟨|Fl|⟩ ⊆
Ψcns(†D≻)|t|; Ψcns(†D≻)⟨Fl ⟩ ⊆
Ψcns(†D≻)|t|
|t|∈|Fl|
|t|∈Fl
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 133
— where the “⊆’s” denote the various local inclusions of diagonal submonoids of
Corollary 3.5, (i), and Propositions 4.1, (iii); 4.3, (iii) — as well as an isomor-
phism
Ψcns(†D≻)0
∼
→ Ψcns(†D≻)⟨Fl ⟩
constituted by the various corresponding local isomorphisms of Corollary 3.5, (iii),
and Propositions 4.1, (iii); 4.3, (iii).
(iv) (Local Theta and Gaussian Monoids) There is a functorial algo-
rithm in the D-prime-strip †D≻ for constructing assignments Ψenv(†D≻), Ψgau(†D≻),
∞Ψenv(†D≻), ∞Ψgau(†D≻)
V ∋ v → Ψenv(†D≻)v
def = Ψenv(†D≻,v); V ∋ v → Ψgau(†D≻)v
def = Ψgau(†D≻,v)
V ∋ v → ∞Ψenv(†D≻)v
def
= ∞Ψenv(†D≻,v)
V ∋ v → ∞Ψgau(†D≻)v
def
= ∞Ψgau(†D≻,v)
— where the various local data are equipped with actions by topological groups
when v ∈ Vnon and splittings [for all v ∈ V], as described in detail in Corollary
3.5, (ii), (iii), and Propositions 4.1, (iv); 4.3, (iv) [cf. also Remarks 4.2.1, (ii),
(iii), (iv); 4.4.1] — as well as compatible evaluation isomorphisms
Ψenv(†D≻)∼
→ Ψgau(†D≻);∞Ψenv(†D≻)∼
→ ∞Ψgau(†D≻)
as described in detail in Corollary 3.5, (ii), and Propositions 4.1, (iv); 4.3, (iv).
(v) (Global Realified Theta and Gaussian Frobenioids) There is a func-
torial algorithm in the D⊢-prime-strip †D⊢
≻ for constructing a Frobenioid
Denv(†D⊢
≻)
— namely, as a copy of the Frobenioid “D (†D⊢
≻)” of (ii) above, multiplied by a
formal symbol“log†D⊢
≻(Θ)” [cf. the constructions of Propositions 4.1, (iv), and
4.3, (iv), as well as of [IUTchI], Example 3.5, (ii)] — isomorphic to the Frobenioid
“Cmod” of [IUTchI], Example 3.5, (i), equipped with a bijection Prime(Denv(†D⊢
≻))
∼
→ V [cf. (ii) above] and, for each v ∈ V, an isomorphism of topological
monoids
∼
ΦDenv(†D⊢
≻),v
→ Ψenv(†D⊢
≻)R
v
— where we write “ΦDenv(†D⊢
≻),v” for the submonoid [isomorphic to R≥0] of the
divisor monoid of Denv(†D⊢
≻) associated to v; we write Ψenv(†D⊢
≻)R
v for the data
[which, as is easily verified, is completely determined by †D⊢
≻ — cf. Propositions
4.1, (ii), (iv), and 4.3, (ii), (iv), as well as the evident analogues of these results
at bad primes, i.e., in the spirit of Remark 4.2.1, (i)] obtained from Ψenv(†D≻)v
[cf. (iv) above] by replacing the ind-topological monoid portion of Ψenv(†D≻)v by the
realification of the quotient of this ind-topological monoid by its submonoid of units.
There is a functorial algorithm in the D⊢-prime-strip †D⊢
≻ for constructing a
subcategory, equipped with a Frobenioid structure,
Dgau(†D⊢
≻) ⊆
j∈Fl
D (†D⊢
≻)j
134 SHINICHI MOCHIZUKI
— [cf. Remark 4.5.2, (i), below concerning the subscript “j’s”] whose divisor and
rational function monoids are determined [relative to the divisor and rational func-
tion monoids of each factor in the product category of the display] by the “vector of
ratios”
...,j2
·
,...
whose components are indexed by j ∈ Fl [cf. Remark 4.5.4 below; the nota-
tional conventions of Propositions 4.1, (iv); 4.3, (iv)] — equipped with a bijection
Prime(Dgau(†D⊢
≻))∼
→ V [cf. (ii) above] and, for each v ∈ V, an isomorphism of
topological monoids
ΦDgau(†D⊢
≻),v
∼
→ Ψgau(†D⊢
≻)R
v
— where we write “ΦDgau(†D⊢
≻),v” for the submonoid [isomorphic to R≥0] of the
divisor monoid of Dgau(†D⊢
≻) associated to v; we write Ψgau(†D⊢
≻)R
v for the data
[which, as is easily verified, is completely determined by †D⊢
≻ — cf. Propositions
4.1, (ii), (iv), and 4.3, (ii), (iv), as well as the evident analogues of these results
at bad primes, i.e., in the spirit of Remark 4.2.1, (i)] obtained from Ψgau(†D≻)v
[cf. (iv) above] by replacing the ind-topological monoid portion of Ψgau(†D≻)v by
the realification of the quotient of this ind-topological monoid by its submonoid of
units. Finally, there is a functorial algorithm in the D⊢-prime-strip †D⊢
≻ for
constructing a global formal evaluation isomorphism of Frobenioids
Denv(†D⊢
≻)∼ → Dgau(†D⊢
≻)
which is compatible, relative to the bijections and local isomorphisms of
topological monoids associated to these Frobenioids, with the local evaluation
isomorphisms of (iv) above.
Proof. The various assertions of Corollary 4.5 follow immediately from the defini-
tions and the references quoted in the statements of these assertions. ⃝
Remark 4.5.1.
(i) Just as was done in Definition 3.8, one may interpret the various collections
of monoids constructed in Corollary 4.5, (i), (iv) as collections of Frobenioids. That
is to say, the collection of monoids discussed in Corollary 4.5, (i), gives rise to an
F-prime-strip, hence also to an associated F⊢-prime-strip. In a similar vein, the
theta and Gaussian monoids of Corollary 4.5, (iv), give rise to a well-defined F⊢
-
prime-strip — up to an indeterminacy, at the v ∈ Vbad [corresponding to the
various 2l-th roots of the square of the theta function and “value-profiles”], relative
to automorphisms of the split Frobenioid at such v ∈ Vbad that induce the identity
automorphism on the subcategory of isometries [cf. [FrdI], Theorem 5.1, (iii)] of
the underlying category of the split Frobenioid — cf. Remark 4.10.1 below. On
the other hand, as discussed in Remark 3.8.1, this Frobenioid-theoretic formulation
is — by comparison to the original monoid-theoretic formulation — technically
ill-suited to discussions of conjugate synchronization.
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 135
(ii) On the other hand, such technical complications do not occur if one re-
stricts oneself to discussions of realifications — cf., e.g., the objects “R≥0(‡D⊢)v”,
“D (‡D⊢)” discussed in Corollary 4.5, (ii). In general, Frobenioid-theoretic formu-
lations are typically technically easier to work with than monoid-theoretic formula-
tions when the associated “Picard groups PicΦ(−)” [cf. [FrdI], Theorem 5.1; [FrdI],
Theorem 6.4, (i); [IUTchI], Remark 3.1.5] contain nontorsion elements — i.e., at
a more intuitive level, when there is a nontrivial notion of the “degree” of a line
bundle. Examples of such Frobenioids include global arithmetic Frobenioids such as
the Frobenioid “D (‡D⊢)” of Corollary 4.5, (ii), as well as the tempered Frobenioids
that appeared in Propositions 3.3 and 3.4; Corollary 3.6.
Remark 4.5.2.
(i) One may also construct symmetrizing isomorphisms as in Corollary
4.5, (iii), for versions labeled by t ∈ LabCusp±(†D≻) of the semi-simplifications
Ψss
cns(†D⊢
≻), equipped with splittings and distinguished elements, and the global re-
alified Frobenioids D (†D⊢
≻), equipped with bijections and local isomorphisms of
topological monoids, as discussed in Corollary 4.5, (iii). We leave the routine de-
tails to the reader.
(ii) Just as was discussed in Remark 3.5.3, one may also consider “multi-
basepoint” versions of the symmetrizing isomorphisms of Corollary 4.5, (iii) [cf.
also the discussion of (i) above] — i.e., by passing to D-Θell-bridges or [holomorphic
or mono-analytic] capsules or processions [cf. [IUTchI], Proposition 6.8, (i), (ii),
(iii); [IUTchI], Proposition 6.9, (i), (ii)]. We leave the routine details to the reader.
Remark 4.5.3. Before proceeding, we pause to review the significance of the
F ±
l -symmetry that gives rise to the symmetrizing isomorphisms of Corollary
4.5, (iii) [cf. Remark 3.5.2].
(i) First, we recall that the crucial conjugate synchronization established
in Corollaries 3.5, (i); 4.5, (iii) [cf. also Propositions 4.1, (iii); 4.3, (iii)], is possible
in the case of the F ±
l -symmetry — but not in the case of the Fl -symmetry! —
precisely because of the connectedness, at each v ∈ V, of the local components
involved — cf. the discussion of Remarks 2.6.1, (i); 2.6.2, (i); 3.5.2, (ii), as well
as [IUTchI], Remark 6.12.4, (i), (ii). Here, we note in passing that although these
remarks essentially only concern v ∈ Vbad, similar [but, in some sense, easier!]
remarks hold at v ∈ Vgood. A related property of the F ±
l -symmetry — which,
again, is not satisfied by the Fl -symmetry! — is the “geometric” nature of the
automorphisms that give rise to this symmetry [cf. Remark 3.5.2, (iii)].
(ii) One way to understand the significance of the “single basepoint” sym-
metrizing isomorphisms arising from the F ±
l -symmetry is to compare these sym-
metrizing isomorphisms with the symmetrizing isomorphisms that arise from the
various“multi-basepoint”[i.e., “multi-connectedcomponent”]symmetriesdiscussed
in Remarks 3.5.3; 4.5.2, (ii). That is to say:
(a) By comparison to the symmetries that arise from mono-analytic cap-
sules/processions: the ring structure — i.e., “arithmetic holomorphic
136 SHINICHI MOCHIZUKI
structure” — that remains intact in the case of the symmetrizing isomor-
phisms of Corollary 4.5, (iii), will play an essential role in the theory of
the log-wall [cf. the discussion of Remark 3.6.4, (i)], which we shall apply
in [IUTchIII].
(b) By comparison to the symmetries that arise from holomorphic cap-
sules/processions: the “single basepoint” that remains intact in the case
of the symmetrizing isomorphisms of Corollary 4.5, (iii), is used not only
to establish conjugate synchronization, but also to maintain a bijective
link with the set of labels in “LabCusp±(−)” [cf. the discussion of Re-
mark 3.5.2]. Both conjugate synchronization and the bijective link with
the set of labels play crucial roles in the theory of Galois-theoretic theta
evaluation developed in §3 [cf. the various remarks following Corollaries
3.5, 3.6; Remark 3.8.3].
(c) By comparison to the symmetries that arise from the F ±
l -symmetries of
D-Θell-bridges: Although the structure of a D-Θell-bridge allows one to
maintain a bijective link with the set of labels in “LabCusp±(−)” [cf. the
discussion of [IUTchI], Remark 4.9.2, (i); [IUTchI], Remark 6.12.4, (i)],
the multi-basepoint nature of the F ±
l -symmetries of D-Θell-bridges does
not allow one to establish conjugate synchronization [cf. (b)].
(iii) Note that in order to glue together the various local F ±
l -symmetries of
Corollary 3.5, (i), and Propositions 4.1, (iii); 4.3, (iii), so as to obtain the global
F ±
l -symmetry of Corollary 4.5, (iii), it is necessary to make use of the global
portion“†D ±” of the D-Θ±ell-Hodge theater under consideration — i.e., by ap-
plying the theory of [IUTchI], Proposition 6.5 [cf. also [IUTchI], Remark 6.12.4,
(iii)]. That is to say, the global portion of the D-Θ±ell-Hodge theater under con-
sideration plays, in particular, the role of
synchronizing the ±-indeterminacies at each v ∈ V.
Indeed, in some sense, this is precisely the content of [IUTchI], Proposition 6.5. In
particular, the essential role played in this context by “†D ±” in synchronizing,
or coordinating, the various local ±-indeterminacies is one important underlying
cause for the profinite conjugacy indeterminacies — i.e.,“Δ”-conjugacy in-
determinacies — that occur in Corollaries 2.4, 2.5 — cf. the discussion of Remark
2.5.2. Thus, in summary, these local ±-indeterminacies constitute one important
reason for the need to apply the “complements on tempered coverings” developed
in [IUTchI], §2, in the proof of Corollary 2.4 of the present paper.
Remark 4.5.4. In the situation of Corollary 4.5, (v), we remark that the Frobe-
nioid Dgau(†D⊢
≻) may be thought of as a sort of “weighted diagonal”, relative to
the weights determined by the vector “(...,j2
·
,...)”. That is to say, at a more
concrete level, the divisor monoid (respectively, rational function monoid) of this
Frobenioid consists of elements of the form
(12
·φ, 22
·φ,..., j2
·φ,...) (respectively, (12
·β, 22
·β,..., j2
·β,...))
— where φ (respectively, β) is an element of the divisor monoid (respectively,
rational function monoid) associated to the Frobenioid D (†D⊢
≻).
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 137
Corollary 4.6. (Frobenioid-theoretic Monoids Associated to Θ±ell
-
Hodge Theaters) Let
†ψΘ±
†HT Θ±ell = (†F≻
±
←− †FT
†ψΘell
±
−→ †D ±)
be a Θ±ell-Hodge theater [relative to the given initial Θ-data — cf. [IUTchI],
Definition 6.11, (iii)] and
‡F= {‡Fv}v∈V
an F-prime-strip; here, we assume [for simplicity] that the D-Θ±ell-Hodge theater
associated to †HT Θ±ell [cf. [IUTchI], Definition 6.11, (iii)] is the D-Θ±ell-Hodge
theater †HT D-Θ±ell
of Corollary 4.5, and that the D-prime-strip associated to ‡F
[cf. [IUTchI], Remark 5.2.1, (i)] is the D-prime-strip ‡D of Corollary 4.5. Also, we
shall denote the F⊢-prime-strip associated to — i.e., the mono-analyticization of
— an F-prime-strip [cf. [IUTchI], Definition 5.2.1, (ii)] by means of a superscript
“⊢”.
(i) (Constant Monoids) There is a functorial algorithm in the F-prime-
strip ‡F for constructing the assignment Ψcns(‡F) given by
Vnon ∋ v → Ψcns(‡F)v
def
= Gv(‡Πv) Ψ‡Fv
Varc ∋ v → Ψcns(‡F)v
def = Ψ‡Fv
— where the data in brackets “{−}” is to be regarded as being well-defined only up
to a ‡Πv-conjugacy indeterminacy — cf. [IUTchI], Definition 5.2, (i); Propo-
sitions 3.3, (ii) [i.e., where we take “†Cv” to be ‡Fv]; 4.2, (i); 4.4, (i). We shall
write
Ψcns(‡F)∼
→ Ψcns(‡D)
for the collection of isomorphisms of data indexed by v ∈ V determined by the
“Kummer-theoretic” isomorphisms of Propositions 3.3, (ii) [i.e., where we take
“†Cv” to be ‡Fv and apply the conventions discussed in Remark 4.2.1., (i); cf. also
Proposition 1.3, (ii), (iii)]; 4.2, (i); 4.4, (i).
(ii) (Mono-analytic Semi-simplifications) There is a functorial algo-
rithm in the F⊢-prime-strip ‡F⊢ for constructing the assignment Ψss
cns(‡F⊢) given
by
V ∋ v → Ψss
cns(‡F⊢)v
def = Ψss
‡F⊢
v
— where we regard each “Ψss
‡F⊢
” as being equipped with its natural splitting and,
v
when v ∈ Vnon, its associated distinguished element; for v ∈ Vnon, “Ψss
” is
‡F⊢
v
to be regarded as being well-defined only up to a †Gv-conjugacy indeterminacy
— cf. Remark 4.2.1, (i), and Propositions 4.2, (ii); 4.4, (ii). We shall write
Ψss
cns(‡F⊢)∼
→ Ψss
cns(‡D⊢)
for the collection of isomorphisms of data indexed by v ∈ V determined by the
“Kummer-theoretic” isomorphisms of Propositions 4.2, (ii); 4.4, (ii) — cf. also
Remark 4.2.1, (i); Corollary 4.5, (ii). Now recall the F -prime-strip
‡F = (‡C , Prime(‡C )∼
→ V,
‡F⊢
, {‡ρv}v∈V)
138 SHINICHI MOCHIZUKI
associated to ‡F in [IUTchI], Remark 5.2.1, (ii). Then, in the notation of Corollary
4.5, (ii); [IUTchI], Remark 5.2.1, (ii), there is an isomorphism of Frobenioids
‡C∼ → D (‡D⊢)
that is uniquely determined by the condition that it be compatible with the
respective bijections Prime(−)∼
→ V and local isomorphisms of topologi-
cal monoids for each v ∈ V, relative to the above collection of isomorphisms
Ψss
cns(‡F⊢)∼
→ Ψss
cns(‡D⊢). Finally, there is a functorial algorithm for construct-
ing from the F -prime-strip ‡F [recalled above] the isomorphism ‡C∼ → D (‡D⊢)
[of the preceding display] and the [necessarily compatible] collection of isomorphisms
Ψss
cns(‡F⊢)∼
→ Ψss
cns(‡D⊢) [cf. Remark 4.6.1 below].
(iii) (Labels, F ±
l -Symmetries, and Conjugate Synchronization) In the
notation of Corollary 4.5, (iii), the collection of isomorphisms of (i) determines,
for each t ∈ LabCusp±(†D≻), a collection of compatible isomorphisms
Ψcns(†F≻)t
∼
→ Ψcns(†D≻)t
— where the †Πv-conjugacy indeterminacy at each v ∈ Vnon [cf. (i)] is in-
dependent of t ∈ LabCusp±(†D≻) — as well as [F ±
l -]symmetrizing isomor-
phisms, induced by the various local F ±
l -actions discussed in Corollary 3.6,
(i), and Propositions 4.2, (iii); 4.4, (iii), between the data indexed by distinct
t ∈ LabCusp±(†D≻). Moreover, these symmetrizing isomorphisms are compat-
ible, relative to †ζ≻ [cf. Corollary 4.5, (iii)], with the F ±
l -symmetry of the
associated D-Θell-bridge [cf. [IUTchI], Proposition 6.8, (i)] and determine [various
diagonal submonoids, as well as] an isomorphism
Ψcns(†F≻)0
∼
→ Ψcns(†F≻)⟨Fl ⟩
constituted by the various corresponding local isomorphisms of Corollary 3.6, (iii),
and Propositions 4.2, (iii); 4.4, (iii).
(iv) (Local Theta and Gaussian Monoids) Let
(†FJ
†ψΘ
−→ †F>
†HT Θ)
be a Θ-bridge [relative to the given initial Θ-data — cf. [IUTchI], Definition
5.5, (ii)] which is glued to the Θ±-bridge associated to the Θ±ell-Hodge theater
†HT Θ±ell via the functorial algorithm of [IUTchI], Proposition 6.7 [so J= T ]
— cf. the discussion of [IUTchI], Remark 6.12.2, (i). Then there is a functo-
rial algorithm in the Θ-bridge of the above display, equipped with its gluing to
the Θ±-bridge associated to †HT Θ±ell
, for constructing assignments ΨFenv(†HT Θ),
ΨFgau(†HT Θ), ∞ΨFenv(†HT Θ), ∞ΨFgau(†HT Θ) [where we make a slight abuse of
the notation “†HT Θ”]
V ∋ v → ΨFenv(†HT Θ)v
def = Ψ†FΘ
v ; V ∋ v → ΨFgau(†HT Θ)v
def = ΨFgau(†F
v)
V ∋ v → ∞ΨFenv(†HT Θ)v
def
= ∞Ψ†FΘ
v
V ∋ v → ∞ΨFgau(†HT Θ)v
def
= ∞ΨFgau(†F
v)
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 139
— where the various local data are equipped with actions by topological groups
when v ∈ Vnon and splittings [for all v ∈ V], as described in detail in Corollary
3.6, (ii), (iii), and Propositions 4.2, (iv); 4.4, (iv) [cf. also Remarks 4.2.1, (ii);
4.4.1] — as well as compatible evaluation isomorphisms
ΨFenv(†HT Θ)∼
→ Ψenv(†D>)∼
→ Ψgau(†D>)∼
→ ΨFgau(†HT Θ);
∞ΨFenv(†HT Θ)∼
→ ∞Ψenv(†D>)∼
→ ∞Ψgau(†D>)∼
→ ∞ΨFgau(†HT Θ)
as described in detail in Corollary 3.6, (ii) [cf. also Remark 4.2.1, (iv); the left-hand
portion of the first display of Proposition 3.4, (i); the first display of Proposition
3.7, (i)], and Propositions 4.2, (iv); 4.4, (iv) [cf. also Corollary 4.5, (iv)].
(v) (Global Realified Theta and Gaussian Frobenioids) By applying —
i.e., in the fashion of the constructions of Propositions 4.2, (iv); 4.4, (iv) — both
labeled [as in (iii) — cf. Remark 4.6.2, (ii), below] and non-labeled versions of the
isomorphism “‡C∼ → D (‡D⊢)” of (ii) to the global Frobenioids “Denv(†D⊢
≻)”,
“Dgau(†D⊢
≻)” constructed in Corollary 4.5, (v), one obtains a functorial algo-
rithm in the Θ-bridge of the first display of (iv), equipped with its gluing to the
Θ±-bridge associated to †HT Θ±ell
, for constructing Frobenioids
Cenv(†HT Θ), Cgau(†HT Θ)
— where again we make a slight abuse of the notation “†HT Θ”; we note in passing
that the construction of “Cenv(†HT Θ)” is essentially similar to the construction of
“Ctht” in [IUTchI], Example 3.5, (ii) — together with bijections Prime(Cenv(†HT Θ))
∼
→ V, Prime(Cgau(†HT Θ))∼
→ V and isomorphisms of topological monoids
ΦCenv(†HT Θ),v
∼
→ ΨFenv(†HT Θ)R
v; ΦCgau(†HT Θ),v
∼
→ ΨFgau(†HT Θ)R
v
[cf. the notational conventions of Corollary 4.5, (v)] for each v ∈ V, as well as
evaluation isomorphisms
Cenv(†HT Θ)∼ → Denv(†D⊢
>)∼ → Dgau(†D⊢
>)∼ → Cgau(†HT Θ)
— i.e., in the fashion of the constructions of Propositions 4.2, (iv); 4.4, (iv), by
“conjugating” the evaluation isomorphism of Corollary 4.5, (v), by the isomorphism
“‡C∼ → D (‡D⊢)” of (ii) — which are compatible, relative to the local iso-
morphisms of topological monoids for each v ∈ V discussed above, with the
local evaluation isomorphisms of (iv).
Proof. The various assertions of Corollary 4.6 follow immediately from the defini-
tions and the references quoted in the statements of these assertions. ⃝
Remark 4.6.1. One verifies easily that, in the case of v ∈ Vnon, the poly-
∼
isomorphism Ψss
→ Ψss
†F⊢
cns(†Gv) of Proposition 4.2, (ii) [cf. also Remark 4.2.1,
v
(i)], may be reconstructed algorithmically from †F⊢
v . By contrast, in the case of
v ∈ Varc, it is not possible to reconstruct algorithmically [the non-unit portion of]
(Group-theoretic Monoids Associated to Base-ΘNF-
140 SHINICHI MOCHIZUKI
∼
thecorrespondingpoly-isomorphismΨss
→Ψss
†F⊢
cns(D⊢
v)ofProposition4.4,(ii),from
v
†F⊢
v . That is to say, in the case of v ∈ Varc, the distinguished element of Ψss
†F⊢
[i.e.,
v
of ΨR
†F⊢
] is not preserved by arbitrary automorphisms of †F⊢
v . On the other hand,
v
in the context of Corollary 4.6, (ii), if one reconstructs both Ψss
cns(‡F⊢)∼
→ Ψss
cns(‡D⊢)
and ‡C∼ → D (‡D⊢) in a compatible fashion, then the distinguished elements at
v ∈ Varc may be computed [in the evident fashion] from the distinguished elements
at v ∈ Vnon, together with the structure of the global Frobenioids ‡C , D (‡D⊢),
i.e., by thinking of these global Frobenioids as “devices for currency exchange”
between the various “local currencies” constituted by the divisor monoids at the
various v ∈ V [cf. [IUTchI], Remark 3.5.1, (ii)].
Remark 4.6.2.
(i) Similar observations to the observations made in Remark 4.5.1, (i), con-
cerning the content of Corollary 4.5, (i), (iv), may be made in the case of Corollary
4.6, (i), (iv).
(ii) Similar observations to the observations made in Remark 4.5.2, (i), (ii),
concerning the content of Corollary 4.5, (iii), may be made in the case of Corollary
4.6, (iii).
Corollary 4.7. Hodge Theaters) Let
†HT D-ΘNF = (†D
†φNF
←− †DJ
†φΘ
−→ †D>)
be a D-ΘNF-Hodge theater [cf. [IUTchI], Definition 4.6, (iii)] which is glued
to the D-Θ±ell-Hodge theater †HT D-Θ±ell
of Corollary 4.5 via the functorial al-
gorithm of [IUTchI], Proposition 6.7 [so J= T ] — cf. the discussion of [IUTchI],
Remark 6.12.2, (i), (ii).
(i) (Non-realified Global Structures) There is a functorial algorithm
in the category †D for constructing the morphism
†D → †D
[i.e., a “category-theoretic version” of the natural morphism of hyperbolic orbicurves
CK → CFmod] of [IUTchI], Example 5.1, (i), the monoid/field/pseudo-monoid
equipped with natural π1(†D )-/(πrat
1 (†D ) )πκ-sol
1 (†D )-actions
π1(†D ) M (†D ), π1(†D ) M (†D ), πκ-sol
1 (†D ) M
∞κ(†D )
— which are well-defined up to π1(†D )-/πκ-sol
1 (†D )-conjugacy indetermina-
cies — of [IUTchI], Example 5.1, (i), the submonoids/subfield/subset of π1(†D/π
rat/κ-sol
1 (†D )-/πκ-sol
1 (†D )-invariants
Mmod(†D ) ⊆ (πκ-sol
1 (†D ) ) Msol(†D ) ⊆ M (†D ),
 )-
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 141
Mmod(†D ) ⊆ M (†D ), Mκ (†D ) ⊆ M
∞κ(†D )
[cf. [IUTchI], Example 5.1, (i)], the [“corresponding”] Frobenioids
Fmod(†D ) ⊆ F (†D ) ← F (†D )
— where we write Fmod(†D ), F (†D ) for the categories “†Fmod”, “†F ” ob-
tained in [IUTchI], Example 5.1, (iii), by taking the “†F ” of loc. cit. to be
F (†D ), and, by abuse of notation, we regard the Frobenioid Fmod(†D ) as being
equipped with a natural bijection
Prime(Fmod(†D ))∼
→ V
[cf. the final portion of [IUTchI], Example 5.1, (v)] — of [IUTchI], Example 5.1,
(ii), (iii), and the natural realification functor
Fmod(†D ) → F R
mod(†D )
[cf. [IUTchI], Example 5.1, (vii); [FrdI], Proposition 5.3].
(ii) (Labels and Fl -Symmetry) Recall the bijection
†ζ : LabCusp(†D )∼
→ J (∼
→ Fl )
of [IUTchI], Proposition 4.7, (iii). In the following, we shall use analogous conven-
tions to the conventions applied in Corollary 4.5 concerning subscripted labels.
Let j ∈ LabCusp(†D ). Then there is a functorial algorithm in the category
†D for constructing an F-prime-strip
F (†D )|j
— which is well-defined up to isomorphism — from F (†D ) [cf. [IUTchI],
Example 5.4, (iv), where we take the “δ” of loc. cit. to be j]. Moreover, the natural
poly-action of Fl on †D [cf. [IUTchI], Example 4.3, (iv)] induces isomorphisms
between the labeled data
F (†D )|j, Mmod(†D )j, Mmod(†D )j,
{πκ-sol
1 (†D ) Msol(†D )}j, {πκ-sol
1 (†D ) M
∞κ(†D )}j,
Fmod(†D )j → F R
mod(†D )j
[cf. (i)] for distinct j ∈ LabCusp(†D ) [cf. Remark 4.7.2 below]. We shall refer
to these isomorphisms as [Fl -]symmetrizing isomorphisms. Here, the objects
equipped with πrat
1 (†D )( πκ-sol
1 (†D ))-actions are to be regarded as being subject
to independent π
rat/κ-sol
1 (†D )-conjugacy indeterminacies for distinct j, to-
gether with a single (πrat
1 (†D ) )πκ-sol
1 (†D )-conjugacy indeterminacy that
is independent of j [cf. the discussion of the final portion of [IUTchI], Exam-
ple 5.1, (i)]. These symmetrizing isomorphisms are compatible, relative to †ζ,
with the Fl -symmetry of the associated D-NF-bridge [cf. [IUTchI], Proposition
142 SHINICHI MOCHIZUKI
4.9, (i)] and determine diagonal F-prime-strips/submonoids/subrings/sub-
pseudo-monoids [equipped with a group action subject to conjugacy indetermina-
cies as described above]/subcategories [cf. Remark 4.7.2 below]
(−)⟨Fl ⟩ ⊆
(−)j
j∈Fl
— where “(−)...” may be taken to be F (†D )|... [cf. the discussion of [IUTchI],
Example 5.4, (i)], Mmod(†D )..., Mmod(†D )..., {πκ-sol
1 (†D ) Msol(†D )}...,
{πκ-sol
1 (†D ) M
∞κ(†D )}..., Fmod(†D )..., or F R
mod(†D )... [cf. the discus-
sion of [IUTchI], Example 5.1, (vii)]. [Here, the notion of a “diagonal F-prime-
strip”, of a “diagonal sub-pseudo-monoid equipped with a group action subject to
conjugacy indeterminacies as described above”, or of a “diagonal subcategory” is
to be understood in a purely formal sense, i.e., as a purely formal notational
shorthand for the Fl -symmetrizing isomorphisms discussed above.]
(iii) (Localization Functors and Realified Global Structures) Let j ∈
LabCusp(†D ). For simplicity, write †Dj= {†Dvj }v∈V,
†D⊢
j= {†D⊢
vj }v∈V for
the D-, D⊢-prime-strips associated [cf. [IUTchI], Definition 4.1, (iv); [IUTchI],
Remark 5.2.1, (i)] to the F-prime-strip F (†D )|j. Then there is a functorial
algorithm in the category †D for constructing [1-]compatible collections of “lo-
calization” functors/poly-morphisms [up to isomorphism]
Fmod(†D )j → F (†D )|j, F R
mod(†D )j → (F (†D )|j)R
{πκ-sol
1 (†D ) M
∞κ(†D )}j → M
∞κv(†Dvj ) ⊆ M
∞κ×v(†Dvj )
v∈V
— where the superscript “R” denotes the realification — as in the discussion
of [IUTchI], Example 5.4, (iv), (vi) [cf. also [IUTchI], Definition 5.2, (v), (vii)],
together with a natural isomorphism of Frobenioids
D (†D⊢
j )∼ → F R
mod(†D )j
[cf. the notation of Corollary 4.5, (ii)] and, for each v ∈ V, a natural isomorphism
of topological monoids
R≥0(†D⊢
j )v
∼
→ Ψ(F (†D )|j)R,v
— where “Ψ(F (†D )|j)R,v” denotes the divisor monoid associated to the Frobe-
nioid that constitutes (F (†D )|j)R at v — which are compatible [cf. Remark
4.7.1 below] with the respective bijections involving “Prime(−)” and the respective
local isomorphisms of topological monoids [cf. the arrow F R
mod(†D )j →
(F (†D )|j)R discussed above; Corollary 4.5, (ii)]. Finally, all of these structures
are compatible with the respective Fl -symmetrizing isomorphisms [cf. (ii)].
Proof. The various assertions of Corollary 4.7 follow immediately from the defini-
tions and the references quoted in the statements of these assertions. ⃝
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 143
Remark 4.7.1. Similar observations to the observations made in Remark 4.5.2,
(i), (ii), concerning the F ±
l -symmetrizing isomorphisms of Corollary 4.5, (iii), may
be made in the case of the Fl -symmetrizing isomorphisms of Corollary 4.7, (ii).
Remark 4.7.2. In the context of Corollary 4.7, (ii), we recall from Remarks
3.5.2, (iii); 4.5.3, (i), that unlike the case with F ±
l -symmetry, in the case of Fl-
symmetry, it is not possible to establish the sort of conjugate synchronization
given in Corollary 4.5, (iii), since the Fl -symmetry involves — i.e., more precisely,
arises from conjugation by elements with nontrivial image in — the arithmetic
portion [i.e., the absolute Galois group of the base field] of the global arithmetic
fundamental groups involved [cf. the discussion of how“GK-conjugacy indeter-
minacies give rise to Gv-conjugacy indeterminacies” in Remark 2.5.2, (iii)]. It is
precisely this state of aﬀairs that obliges us, in Corollary 4.7, (ii), to work with
(a) F-prime-strips,asopposedtothecorrespondingind-topological monoids
with Galois actions as in Corollary 4.5, (iii), and with
(b) the various objects introduced in Corollary 4.7, (i), that are equipped
with sub-/super-scripts
“mod”, “sol”, “κ-sol”, or “∞κ”
— corresponding to “Fmod”, “Fsol”, “πκ-sol
1 (−)”, or “∞κ-coric rational
functions” — or [as in the case of “π
rat/κ-sol
1 (−)”] are only defined up
to certain conjugacy indeterminacies, as opposed to the objects not
equipped with such subscripts or not subject to such conjugacy indeter-
minacies.
That is to say, both (a) and (b) allow one to ignore the various independent — i.e.,
non-synchronizable— conjugacy indeterminacies that occur at the various distinct
labels as a consequence of the single basepoint with respect to which one consid-
ers both the labels and the labeled objects [cf. the discussion of Remark 3.5.2, (ii)].
Here, itisalsousefulto observethat byworkingwiththe variousobjectsintroduced
in Corollary 4.7, (i), that are equipped with a sub-/super-script “mod”, “sol”, or
“κ-sol” — i.e., on which the various conjugacy indeterminacies involved act in a
synchronized fashion — one may construct the various diagonal subcategories as-
sociated to the corresponding Frobenioids in a fashion in which one is not obliged
to contend with the technical subtleties that arise from independent conjugacy
indeterminacies at distinct labels [cf. the discussion of “Galois-invariants/Galois-
orbits” in Remark 3.8.3, (ii)]. In [IUTchIII], the ring structure on these objects
equipped with a subscript “mod” will be applied as a sort of translation appara-
tus between “ -line bundles” [i.e., arithmetic line bundles thought of as additive
moduleswithadditionalstructure]and“ -line bundles” [i.e., arithmeticlinebun-
dles thought of “multiplicatively” or “id` elically”, as in the theory of Frobenioids]
— cf. [AbsTopIII], Definition 5.3, (i), (ii).
Remark 4.7.3. At this point, it is of interest to review the significance of the
F ±
l - and Fl -symmetries in the context of the theory of the present §4.
(i) First, we recall that, in the context of the present series of papers, the “Fl
”
that appears in the notation “F ±
l ” and “Fl ” is to be thought of — since l is
144 SHINICHI MOCHIZUKI
“large” — as a sort of finite approximation of the ring of rational integers Z [cf.
the discussion of [IUTchI], Remark 6.12.3, (i)]. That is to say, the F ±
l -symmetry
corresponds to the additive structure of Z, while the Fl -symmetry corresponds
to the multiplicative structure of Z. Since the “Fl” under consideration arises
from the torsion points of an elliptic curve, it is natural — especially in light of
the central role played in the present series of papers by v ∈ Vbad — to think of
the “Z” under consideration as the Galois group “Z” of the universal combinatorial
covering of the Tate curves that appear at v ∈ Vbad [cf. the discussion at the
beginning of [EtTh], §1]. In particular, in light of the theory of Tate curves, it is
natural to think of this “Z” as representing a sort of universal version of the value
group associated to a local field that occurs at a v ∈ Vbad, and to think of the
element 0 ∈ Z — hence, the label
0 ∈ |Fl|
— as representing the units.
(ii) Perhaps the most fundamental diﬀerence between the F ±
l - and Fl -sym-
metries lies in the fact that the F ±
l -symmetry involves the zero label 0 ∈ |Fl|
[cf. the discussion of [IUTchI], Remark 6.12.5]. In particular, the F ±
l -symmetry
is suited to application to the “units” — i.e., to the various local “O×” and “O×μ”
that appear in the theory. At a more technical level, this relationship between the
F ±
l -symmetry and “O×” may be seen in the theory of §3 [cf. also Corollaries 4.5,
(iii); 4.6, (iii)]. That is to say, in §3 [cf. the discussion of Remark 3.8.3], the F ±
l-
symmetry is applied precisely to establish conjugate synchronization, which,
in turn, will be applied eventually to establish the crucial coricity of “O×μ” in
the context of the Θ×μ
gau-link [cf. Corollary 4.10, (iv), below]. Here, let us observe
that the conjugate synchronization, established by means of the F ±
l -symmetry, of
copies of the absolute Galois group of the local base field at various v ∈ Vnon is a
verydelicatepropertythatdepends quite essentially on the “arithmetic holomorphic
structure” of the Hodge theaters under consideration. That is to say, from the point
of view of the theory of §1, conjugate synchronization in one Hodge theater fails
to be compatible with conjugate synchronization in another Hodge theater with a
distinct arithmetic holomorphic structure. Put another way, from the point of view
of the theory of §1, conjugate synchronization can only be naturally formulated in
a uniradial fashion. This uniradiality may also be seen at a purely combinatorial
level, as we shall discuss in Remark 4.7.4 below. On the other hand, if one passes to
mono-analyticizations — e.g., to mono-analytic processions — then the mono-
analytic“O×μ” that appears in the Θ×μ
gau-link [cf. Corollary 4.10, (iv), below] is,
by contrast, coric. That is to say, by relating the zero label, which is common
to distinct arithmetic holomorphic structures, to the various nonzero labels, which
belongtoasingle fixed arithmetic holomorphic structure, theconditionofinvariance
with respect to the F ±
l -symmetry may — e.g., in the case of the mono-analytic
“O×μ” — amount to a condition of coricity. In particular, in the case of the
mono-analytic“O×μ”,
the F ±
l -symmetry plays the role of establishing the coric pieces — i.e.,
components which are “uniform” with respect to all of the distinct arith-
metic holomorphic structures involved — of the apparatus to be estab-
lished in the present series of papers.
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 145
This dual role — i.e., consisting of both uniradial and coric aspects — played by
the F ±
l -symmetry is to be considered in contrast to the strictly multiradial role
[cf. (iii) below] played by the Fl -symmetry. Also, in this context, we observe that
the symmetrization, eﬀected by the F ±
l -symmetry, between zero and nonzero
labels may be thought of, from the point of view of (i), as a symmetrization between
[local] units and value groups and, hence, in particular, is reminiscent of the
intertwining of units and value groups eﬀected by the log-link [cf. [IUTchIII],
Remark 3.12.2, (i), (ii)], as well as of the crucial compatibility between the F ±
l-
symmetrizing isomorphisms [i.e., that give rise to the conjugate synchronization]
and the log-link [cf. [IUTchIII], Remark 1.3.2].
(iii) The significance of the Fl -symmetry lies, in a word, in the fact that it
allows one to separate the zero label from the nonzero labels. From the point
of view of the theory of the present series of papers, this property makes the Fl-
symmetry well-suited for the construction/description of the internal structure of
the Gaussian monoids, which are, in eﬀect, “distributions” or “functions” of a
parameter j ∈ Fl [cf. Corollaries 4.5, (iv), (v); 4.6, (iv), (v)]. Here, we note that
this separation of the zero label — which parametrizes coric data that is common
to distinct arithmetic holomorphic structures — from the nonzero labels — which
parametrize the components of the Gaussian monoid associated to a particular
arithmetic holomorphic structure — is crucial from the point of view of describing
the Gaussian monoid associated to a particular arithmetic holomorphic structure
in terms that may be understood from the point of view of some “alien” arithmetic
holomorphic structure. Put another way, from the point of view of the theory of §1,
the Fl -symmetry admits a natural multiradial formulation. This multiradiality
may also be seen at a purely combinatorial level, as we shall discuss in Remark
4.7.4 below. In this context, it is important to note that if one thinks of the coric
constant distribution, labeled by zero, as embedded via the diagonal embedding into
the various products parametrized by j ∈ Fl that appear in the construction of
the Gaussian monoids [cf. the isomorphisms that appear in the final displays of
Corollaries4.5, (iii); 4.6, (iii)], thenitisnaturaltothinkofthevolumescomputedat
eachj ∈ Fl asbeingassignedaweight 1/l —i.e., sothatthediagonalembedding
of the constant distribution is compatible with taking the constant distribution to
be of weight 1 [cf. the discussion of [IUTchI], Remark 5.4.2]. Put another way,
from the point of view of “computation of weighted volumes”, the various nonzero
j ∈ Fl are “subordinate” to 0 ∈ |Fl| — i.e., Fl ∋ j ≪ 0. In particular, to
symmetrize, in the context of the internal structure of the Gaussian monoids, the
zero and nonzero labels [i.e., as in the case of the F ±
l -symmetry!] amounts to
allowing a relation
“0 ≪ 0”
— which is absurd [i.e., in the sense that it fails to be compatible with weighted
volume computations]!
Remark 4.7.4.
(i) One way to understand the underlying combinatorial structure of the
uniradiality oftheF ±
l -symmetryandthemultiradiality oftheFl -symmetry[cf.
the discussion of Remark 4.7.3, (ii), (iii)] is to consider these symmetries — which
146 SHINICHI MOCHIZUKI
are defined relative to some given arithmetic holomorphic structure [or, at a more
technical level, some given Θ±ellNF-Hodge theater — cf. [IUTchI], Definition 6.13,
(i)] — in the contextof the´ etale-pictures that arise from each of these symmetries
[cf. [IUTchI], Corollaries 4.12, 6.10]. In the case of the F ±
l - (respectively, Fl -)
symmetry, this ´ etale-picture consists of a collection of copies of Fl (respectively,
|Fl|= Fl {0}), each copy corresponding to a single arithmetic holomorphic
structure, which are glued together at the coric label 0 ∈ Fl (respectively, 0 ∈ |Fl|).
In Fig. 4.1 (respectively, 4.2) below, an illustration is given of such an´ etale-picture,
in which the notation “±” (respectively, “ ”) is used to denote the various elements
of Fl \{0} (respectively, Fl ) in each copy of Fl (respectively, |Fl|). Moreover, on
each copy of Fl (respectively, |Fl|) — labeled, say, by some spoke α [corresponding
to a single arithmetic holomorphic structure] — one has a natural action of a
“corresponding copy” of F ±
l (respectively, Fl ).
(ii) The fundamental diﬀerence between the simple combinatorial models of
the ´ etale-pictures considered in (i) lies in the fact that whereas
(a) in the case of the F ±
l -symmetry, the F ±
l -actions on distinct spokes fail
to commute with one another,
(b) in the case of the Fl -symmetry, the Fl -actions on distinct spokes com-
mute with one another and, moreover, are compatible with the permu-
tations of spokes discussed in [IUTchI], Corollary 4.12, (iii).
Indeed, the noncommutativity, or “incompatibility with simultaneous execution at
distinct spokes” [cf. Remark 1.9.1], of (a) is a direct consequence of the inclusion
of the zero label in the F ±
l -symmetry and may be thought of as a sort of pro-
totypical combinatorial representation of the phenomenon of uniradiality.
By contrast, the commutativity, or “compatibility with simultaneous execution at
distinct spokes” [cf. Remark 1.9.1], of (b) is a direct consequence of the exclusion of
the zero label from the Fl -symmetry and may be thought of as a sort of prototypi-
cal combinatorial representation of the phenomenon of multiradiality. Note that
in the case of the F ±
l -symmetry, it is also a direct consequence of the inclusion
of the zero label that the condition of invariance with respect to the F ±
l -actions
on all of the spokes may be thought of as a condition of “uniformity” among the
elements of the copies of Fl at the various spokes, hence as a sort of coricity [cf.
the discussion of Remark 4.7.3, (ii)].
...
± ±
± ±
± ±
± ±...
↓ ↑
→
← 0 ←
→
± ±
± ±
Fig. 4.1:
´
Etale-picture of F ±
l -symmetries
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 147
... ...
|
— 0 —
´
Fig. 4.2:
Etale-picture of Fl -symmetries
(iii) Although the combinatorial versions of uniradiality and multiradiality dis-
cussed in (ii) above are not formulated in terms of the formalism of uniradial and
multiradial environments developed in §1 [cf. Example 1.7, (ii)], it is not diﬃcult to
produce such a formulation. For instance, one may take the coric data to consist of
objects of the form “0α” — i.e., the zero label, subscripted by the label α associated
to some spoke. For any two spokes α, β, we define the set of arrows
0α → 0β
to consist of precisely one element (α,β). We then take, in the case of the F ±
l-
(respectively, Fl -)symmetry, theradial datatoconsistofacopy(Fl)α (respectively,
|Fl|α) of Fl (respectively, |Fl|) subscripted by the label α associated to some spoke.
For any two spokes α, β, we define the set of arrows
(Fl)α → (Fl)β (respectively, |Fl|α → |Fl|β)
to consist of precisely one element if the actions (F ±
l )γ (Fl)γ (respectively,
(Fl )γ (|Fl|)γ), for γ= α,β, determine an action of
(F ±
l )α × (F ±
l )β (respectively, (Fl )α × (Fl )β)
on the co-product (Fl)α 0 (Fl)β (respectively, (|Fl|)α 0 (|Fl|)β) obtained by
identifying the respective zero labels 0α, 0β, and to equal the empty set if such
an action does not exist. Then one has a natural radial functor (Fl)α → 0α
(respectively, |Fl|α → 0α) that associates coric data to radial data. Moreover, the
resultingradial environmentiseasilyseentobeuniradial(respectively, multiradial).
We leave the routine details to the reader. Finally, we note in passing that the
formulation involving products given above is reminiscent both of the discussion of
the switching functor in Example 1.7, (iii), and of the discussion of parallel transport
via connections in Remark 1.7.1.
Remark 4.7.5. In the context of the discussion of the combinatorial models
of the F ±
l - and Fl -symmetries in Remark 4.7.4, it is useful to recall that the
F ±
l -andFl -symmetriescorrespond, respectively, totheadditiveandmultiplicative
structures of the field Fl — which [cf. Remark 4.7.3, (i)] we wish to think of as a
sort of finite approximation of the ring Z. That is to say, from the point of view of
the theory of the present series of papers,
(a) the F ±
l - and Fl -symmetries correspond, respectively, to the two com-
binatorial dimensions — i.e., addition and multiplication — of a ring [cf.
the discussion of [AbsTopIII], §I3].
148 SHINICHI MOCHIZUKI
Moreover, in the context of the discussion of Remark 4.7.3, (i), concerning units
and value groups, it is useful to recall that these two combinatorial dimensions may
be thought of as corresponding to
(b) the units and value group of a mixed-characteristic nonarchimedean or
complex archimedean local field [cf. the discussion of [AbsTopIII], §I3]
or, alternatively, to
(c) the two cohomological dimensions of the absolute Galois group of a
mixed-characteristic nonarchimedean local field or the two underlying real
dimensions of a complex archimedean local field [cf. the discussion of
[AbsTopIII], §I3].
Finally, the hierarchical structure of these two dimensions — i.e., the way in which
“one dimension [i.e., multiplication] is piled on top of the other [i.e., addition]”—
is reflected in the
(d) subordination structure “≪”, relative to the computation of weighted
volumes, of nonzero labels with respect to the zero label [cf. the discussion
of Remark 4.7.3, (iii)].
as well as in the fact that
(e) the F ±
l -symmetry arises from the conjugation action of the geometric
fundamental group [cf. Remarks 3.5.2, (iii); 4.5.3, (i)], whereas the Fl-
symmetry arises from the conjugation action of the absolute Galois group
of the global base field [cf. Remark 4.7.2]
— i.e., where we recall that the arithmetic fundamental groups involved may be
thought of as having a natural hierarchical structure constituted by their extension
structure [corresponding to the natural outer action of the absolute Galois group of
the base field on the geometric fundamental group].
Remark 4.7.6. One important observation in the context of Corollary 4.7, (i),
is that it makes sense to consider non-realified global Frobenioids [correspond-
ing, e.g., to “Fmod”] only in the case of the Fl -symmetry. Indeed, in order to
consider the field “Fmod” from an anabelian, or Galois-theoretic, point of view, it
is necessary to consider the full profinite group ΠCF — i.e., not just the open sub-
groups ΠCK , ΠXK
of ΠCF which give rise, respectively, to the global portions of the
Fl - and F ±
l -symmetries [cf. [IUTchI], Definition 4.1, (v); [IUTchI], Definition 6.1,
(v)]. On the other hand, to work with the abstract topological group ΠCF means
that the subgroups ΠCK , ΠXK
of ΠCF are only well-defined up to ΠCF -conjugacy.
That is to say, in this context, the subgroups ΠCK , ΠXK are only well-defined
up to automorphisms arising from their normalizers in ΠCF [cf. the discussion
of [IUTchI], Remark 6.12.6, (iii), (iv)]. In particular, in the present context, one
is obliged to regard these groups ΠCK , ΠXK as being subject to indeterminacies
arising from the natural Fl -poly-actions [i.e., actions by a group that surjects nat-
urally onto Fl — cf. [IUTchI], Example 4.3, (iv)] on these groups — that is to
say, subject to indeterminacies arising from the natural Fl -symmetries of these
groups. Here, it is important to note that one cannot simply “form the quotient
by the indeterminacy constituted by these Fl -symmetries” since this would give
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 149
rise to “label-crushing”, i.e., to identifying to a single point the distinct labels
j ∈ Fl , which play a crucial role in the construction of the Gaussian monoids [cf.
the discussion of [IUTchI], Remark 4.7.1]. But then the Fl -symmetries of ΠCK ,
ΠXK that one must contend with necessarily involve conjugation by elements of the
absolute Galois groups of the global base fields involved, hence are fundamentally
incompatible with the establishment of conjugate synchronization [cf. the discussion
of Remark 4.7.2]. That is to say, just as it is necessary to
(a) isolate the F ±
l -symmetry from the Fl -symmetry in order to establish
conjugate synchronization [cf. the discussion of Remark 4.7.2],
it is also necessary to
(b) isolate the Fl -symmetry from the F ±
l -symmetry in order to work
with Galois-theoretic representations of the global base field Fmod.
Indeed, in this context, it is useful to recall that one of the fundamental themes
of the theory of the present series of papers consists precisely of the dismantling
of the two [a priori intertwined!] combinatorial dimensions of a ring [cf. Remarks
4.7.3, 4.7.5; [AbsTopIII], §I3].
Remark 4.7.7. The theory of “tempered versus profinite conjugates” developed
in [IUTchI], §2, is applied in the proof of Corollary 2.4, (i), in a setting which
ultimately [cf. Remark 2.6.2, (i); Corollary 4.5, (iii)] is seen to amount to a certain
local portion [at v ∈ Vbad] of a [D-]Θ±ell-Hodge theater — i.e., a setting in
which one considers the F ±
l -symmetry. On the other hand, in [IUTchI], Remark
4.5.1, (iii), a discussion is given in which this theory of “tempered versus profinite
conjugates” developed in [IUTchI], §2, is applied in a setting which constitutes a
certain local portion [at v ∈ Vbad] of a [D-]ΘNF-Hodge theater. In this context,
it is useful to note that the point of view of this discussion given in [IUTchI],
Remark 4.5.1, (iii), may be regarded as “implicit” in the point of view of the theory
of the present §4 in the following sense: The profinite conjugacy indeterminacies
that occur in an [D-]ΘNF-Hodge theater [cf. [IUTchI], Remark 4.5.1, (iii)] are
linked via the gluing operation discussed in [IUTchI], Remark 6.12.2, (i), (ii) — cf.
Corollaries 4.6, (iv); 4.7 — to the profinite conjugacy indeterminacies that occur
in an [D-]Θ±ell-Hodge theater [cf. Remarks 2.5.2, (ii), (iii); 2.6.2, (i); 4.5.3, (iii)],
i.e., to the profinite conjugacy indeterminacies that are “resolved” in the proof of
Corollary 2.4, (i), by applying the theory of [IUTchI], §2.
Corollary 4.8. Hodge Theaters) Let
(Frobenioid-theoretic Monoids Associated to ΘNF-
†HT ΘNF = (†F †F
†ψNF
←− †FJ
†ψΘ
−→ †F>
†HT Θ)
be a ΘNF-Hodge theater [cf. [IUTchI], Definition 5.5, (iii)] which lifts the D-
ΘNF-Hodge theater †HT D-ΘNF of Corollary 4.7 and is glued to the Θ±ell-Hodge
theater †HT Θ±ell of Corollary 4.6 via the functorial algorithm of [IUTchI], Propo-
sition 6.7 [so J= T ] — cf. the discussion of [IUTchI], Remark 6.12.2, (i), (ii).
150 SHINICHI MOCHIZUKI
(i) (Non-realified Global Structures) There is a functorial algorithm
in the category †F [or in the category †F ] — cf. the discussion of [IUTchI], Ex-
ample 5.1, (v), (vi), concerning isomorphisms of cyclotomes and related Kum-
mer maps — for constructing Kummer isomorphisms of pseudo-monoids
[the first two of which are equipped with group actions and well-defined up to a
single conjugacy indeterminacy]
πκ-sol
1 (†D ) †M
∞κ
∼
→ πκ-sol
1 (†D ) M
∞κ(†D ),
†Mκ
∼
→ Mκ (†D )
and, hence, by restricting Kummer classes as in the discussion of [IUTchI],
Example 5.1, (v), natural “Kummer-theoretic” isomorphisms
π1(†D ) †M∼
→ π1(†D ) M (†D )
π1(†D ) †M∼
→ π1(†D ) M (†D )
πκ-sol
1 (†D ) †Msol
∼
→ πκ-sol
1 (†D ) Msol(†D )
†Mmod
∼
→ Mmod(†D ),
†Mmod
∼
→ Mmod(†D )
— which may be interpreted as a compatible collection of isomorphisms of
Frobenioids
†Fmod
†F∼ → F (†D ),
∼ → Fmod(†D ),
†F∼ → F (†D )
†F R
∼ → F R
mod
mod(†D )
[cf. the discussion of [IUTchI], Example 5.1, (ii), (iii)].
(ii) (Labels and Fl -Symmetry) In the notation of Corollary 4.7, (ii), the
collection of isomorphisms of Corollary 4.6, (i) [applied to the F-prime-strips of
the capsule †FJ; cf. also the discussion of [IUTchI], Example 5.4, (iv)], together
with the isomorphisms of (i) above, determine, for each j ∈ LabCusp(†D ) (∼
→ J)
[cf. the bijection †ζ of Corollary 4.7, (ii)], a collection of isomorphisms
†Fj
∼
→ †F |j
∼ → F (†D )|j
(†Mmod)j
∼
→ Mmod(†D )j, (†Mmod)j
∼
→ Mmod(†D )j
{πκ-sol
1 (†D ) †Msol}j
∼ → {πκ-sol
1 (†D ) Msol(†D )}j
{πκ-sol
1 (†D ) †M
∞κ}j
∼ → {πκ-sol
1 (†D ) M
∞κ(†D )}j
(†Fmod)j
∼ → Fmod(†D )j, (†F R
mod)j
∼ → F R
mod(†D )j
as well as [Fl -]symmetrizing isomorphisms, induced by the natural poly-action
of Fl on †F [cf. [IUTchI], Example 4.3, (iv); [IUTchI], Corollary 5.3, (i)], be-
tween the data indexed by distinct j ∈ LabCusp(†D ). Here, [just as in Corollary
4.7, (ii)] the objects equipped with πrat
1 (†D )( πκ-sol
1 (†D ))-actions are to be re-
garded as being subject to independent π
rat/κ-sol
1 (†D )-conjugacy indetermina-
cies for distinct j, together with a single (πrat
1 (†D ) )πκ-sol
1 (†D )-conjugacy
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 151
indeterminacy that is independent of j [cf. the discussion of the final portion of
[IUTchI], Example 5.1, (i)]. Moreover, these symmetrizing isomorphisms are com-
patible, relative to †ζ [cf. Corollary 4.7, (ii)], with the Fl -symmetry of the as-
sociated NF-bridge [cf. [IUTchI], Proposition 4.9, (i); [IUTchI], Corollary 5.6, (ii)]
and determine various diagonal F-prime-strips/submonoids/subrings/sub-
pseudo-monoids [equipped with a group action subject to conjugacy indetermina-
cies as described above]/subcategories
(−)⟨Fl ⟩ ⊆
(−)j
j∈Fl
[i.e., relative to the conventions discussed in Corollary 4.7, (ii); cf. also Remark
4.7.2].
(iii) (Localization Functors and Realified Global Structures) Let j ∈
LabCusp(†D ). In the following, objects associated to an F-prime-strip labeled by
j at an element v ∈ Vmod will be denoted by means of a label “vj”. Then there is
a functorial algorithm in the NF-bridge (†FJ → †F †F ) for constructing
mutually [1-]compatible collections of “localization” functors/poly-morphisms
[up to isomorphism]
(†Fmod)j → †Fj, (†F R
mod)j → †FR
j
{πκ-sol
1 (†D ) †M
∞κ}j → †M
∞κvj ⊆ †M
∞κ×vj
v∈V
as in the discussion of [IUTchI], Example 5.4, (iv), (vi) [cf. also [IUTchI], Defini-
tion 5.2, (vi), (viii)] — which are compatible, relative to the various [Kummer/
“Kummer-theoretic”] isomorphisms of (i), (ii) [cf. also [IUTchI], Definition 5.2,
(vi), (viii)], with the collections of functors/poly-morphisms of Corollary 4.7, (iii)
— together with a natural isomorphism of Frobenioids
†Cj
∼
→ (†F R
mod)j
[cf. the notation of Corollary 4.6, (ii); [IUTchI], Remark 5.2.1, (ii), applied to
the F-prime-strip †Fj] which is compatible [cf. Remark 4.8.3 below] with the
respective bijections involving “Prime(−)”, the respective local isomorphisms
of topological monoids [cf. the arrow (†F R
mod)j → †FR
j discussed above;
[IUTchI], Remark 5.2.1, (ii)], the isomorphisms of Corollary 4.7, (iii), and the vari-
ous [“Kummer-theoretic”] isomorphisms of (i), (ii) [cf. also Corollary 4.6, (ii)]. Fi-
nally, all of these structures are compatible with the respective Fl -symmetrizing
isomorphisms [cf. (ii)].
Proof. The various assertions of Corollary 4.8 follow immediately from the defini-
tions and the references quoted in the statements of these assertions. ⃝
Remark 4.8.1.
(i) The Frobenioid Cgau(†HT Θ) of Corollary 4.6, (v), is constructed as a sub-
category of a product over j ∈ Fl of copies †Cj of the category †C . In particular,
152 SHINICHI MOCHIZUKI
one may apply the isomorphism †Cj
this Frobenioid Cgau(†HT Θ) as a subcategory
∼
→ (†F R
mod)j of Corollary 4.8, (iii), to regard
Cgau(†HT Θ) →
(†F R
mod)j
j∈Fl
of the product over j ∈ Fl of the (†F R
mod)j.
(ii) In a similar vein, the local data at v ∈ V of the objects ΨFgau(†HT Θ)
constructed in Corollary 4.6, (iv), gives rise to [the local data at v of an F⊢-prime-
strip, i.e., in particular, to] split Frobenioids Fgau(†HT Θ)v [cf. Definition 3.8, (ii),
in the case of v ∈ Vbad]. Write Fgau(†HT Θ) for the F⊢-prime-strip determined by
this local data Fgau(†HT Θ)v at v, for v ∈ V, and
Fgau(†HT Θ)R
for the object obtained by forming, at each v ∈ V, the realification of the underlying
Frobenioid of Fgau(†HT Θ) at v. Then it follows from the construction discussed in
Corollary 4.6, (iv), that one may think of the realified Frobenioid, at each v ∈ V,
of Fgau(†HT Θ)R as being naturally [“poly-”]embedded
Fgau(†HT Θ)R →
(†FR
>)j
j∈Fl
[where we use this notation to denote the collection of [“poly-”]embeddings indexed
by v ∈ V] in the product of copies of realifications of [the underlying Frobenioids
of] the F-prime-strip †F> labeled by j ∈ Fl . Moreover, by applying the full poly-
isomorphisms (†F>)j
∼
→ †Fj — which are tautologically compatible with the labels
j ∈ Fl ! — we may think of Fgau(†HT Θ)R as being naturally [“poly-”]embedded
Fgau(†HT Θ)R →
†FR
j
j∈Fl
[where we use this notation to denote the collection of [“poly-”]embeddings in-
dexed by v ∈ V] in the product associated to the realifications of [the underlying
Frobenioids of] the F-prime-strips †Fj.
(iii) Thus, by applying the various [“poly-”]embeddings considered in (i), (ii),
one may think of the “realified localization” functors
(†F R
mod)j → †FR
j
of Corollary 4.8, (iii), as inducing a “realified localization” functor [up to isomor-
phism]
Cgau(†HT Θ) → Fgau(†HT Θ)R
— which [as one verifies immediately] is compatible [cf. the various compatibil-
ities discussed in Corollary 4.8, (iii)] with the realified localization isomorphisms
∼
ΦCgau(†HT Θ),v
→ ΨFgau(†HT Θ)R
v, for v ∈ V, considered in Corollary 4.6, (v).
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 153
Remark 4.8.2.
(i) The realified localization functor discussed in Remark 4.8.1, (iii), only
concerns the realification of the Frobenioid-theoretic version Fgau(†HT Θ) of the
Gaussian monoids. The unit portion of the Gaussian monoids will be used, in
the context of the theory involving the log-wall that will be developed in [IUTchIII],
not in its capacity as a “multiplicative object”, but rather — i.e., by applying the
operation “log” to the units at the various v ∈ V, as in the theory of [AbsTopIII]
— as an “additive object”. In this theory, the non-realified global Frobenioids of
Corollary 4.8, (i), will appear in the context of localization functors/morphisms —
i.e., as a sort of translation apparatus between - and -line bundles [cf. the
discussion of Remark 4.7.2] — that relate these [multiplicative!] non-realified global
Frobenioids to the [additive!] images via “log” of the units. Note that this sort of
construction — i.e., in which the localization operations involving units and value
groups diﬀer by a shift via the operation “log” — depends, in an essential way [cf.
the discussion of Remark 1.12.2, (iv)], on the natural splittings with which the
Gaussian monoids are equipped [cf. Corollary 4.6, (iv)].
(ii) In the context of (i), it is useful to observe that, although the non-realified
global Frobenioids of Corollary 4.8, (i), may only be considered in the context of the
Fl -symmetry [cf. the discussion of Remark 4.7.6], this does not yield any obstacles,
relative to the discussion in (i) of Gaussian monoids, since Gaussian monoids are
most naturally considered as “functions” of a parameter j ∈ Fl [cf. the discussion
of Remark 4.7.3, (iii)].
(iii) From the point of view of the analogy of the theory of the present series
of papers with p-adic Teichm¨ uller theory [cf. the discussion of [AbsTopIII], §I5], it
is of interest to note that the construction discussed in (i) involving the use of the
natural splittings of Gaussian monoids to consider“log-shifted units” together with
“non-log-shifted value groups” may be thought of as corresponding to the situation
that frequently occurs in p-adic Teichm¨ uller theory in which an indigenous bundle
(E,∇E)equippedwithaHodge filtration0 → ω → E → τ → 0onahyperboliccurve
in positive characteristic is represented, in the context of local Frobenius liftings
modulo higher powers of p, as a direct sum
Φ∗
τ ⊕ ω
— where Φ denotes the Frobenius morphism on the curve, which, as may be recalled
from the discussion of [AbsTopIII], §I5, corresponds, relative to the analogy under
consideration, to the operation “log” studied in [AbsTopIII].
Remark 4.8.3. Similar observations to the observations made in Remark 4.5.2,
(i), (ii), concerning the F ±
l -symmetrizing isomorphisms of Corollary 4.5, (iii), may
be made in the case of the Fl -symmetrizing isomorphisms of Corollary 4.8, (ii).
Definition 4.9.
(i) Let C be an arbitrary Frobenioid. Write D for the base category of C.
Suppose that D is isomorphic to the category of connected finite ´ etale coverings
154 SHINICHI MOCHIZUKI
of the spectrum of an MLF or a CAF. Let A be a “universal covering pro-object”
of D [cf. the discussion of Example 3.2, (i), (ii)]. Write G def = Aut(A) [so G is
isomorphic to the absolute Galois group of an MLF or a CAF]. Now by evaluating
the monoid “O◃(−)” on D that arises from the general theory of Frobenioids [cf.
[FrdI], Proposition 2.2] at A, we thus obtain a monoid [in the usual sense] equipped
with a natural action by G
G O◃(A)
[cf. the discussion of Example 3.2, (ii)]. If N is a positive integer, then we shall
write
μN(A) ⊆ Oμ(A) ⊆ O×(A)
for the subgroups of N-torsion elements [cf. [FrdII], Definition 2.1, (i)] and torsion
elements of arbitrary order;
O×(A) O×μN (A) O×μ(A)
for the respective quotients of the submonoid of units O×(A) ⊆ O◃(A) by μN(A),
Oμ(A). Thus, O◃(A), O×(A), O×μN (A), O×μ(A), μN(A), and Oμ(A) are all
equipped with natural G-actions. Next, let us suppose that G is nontrivial [i.e.,
arises from an MLF]. Recall the group-theoretic algorithms“G → (G O×(G))”
and “G → (G O×μ(G))” discussed in Example 1.8, (iii), (iv). We define
a ×-Kummer structure (respectively, ×μ-Kummer structure) on C to be a Z×
-
(respectively, Ism- [cf. Example 1.8, (iv)]) orbit of isomorphisms
κ× : O×(G)∼ → O×(A) (respectively, κ×μ : O×μ(G)∼ → O×μ(A))
of ind-topological G-modules. Note that since any two “universal covering pro-
objects” of D are isomorphic, it follows immediately that the definition of a ×-
(respectively, ×μ-) Kummer structure is independent of the choice of A. Next, let
us recall from Remark 1.11.1, (b), that
any ×-Kummer structure on C is unique.
In the case of ×μ-Kummer structures, let us observe that a ×μ-Kummer structure
κ×μ on C determines, for each open subgroup H ⊆ G, a submodule
Iκ
H(A) def = Im(O×(G)H) ⊆ O×μ(A)
— namely, the image via κ×μ of the image of O×(G)H in O×μ(G)H [where the
superscript “H’s” denote the submodules of H-invariants]. Conversely, it is es-
sentially a tautology [cf. the definition of “Ism” given in Example 1.8, (iv)!] that
the ×μ-Kummer structure κ×μ on C is completely determined by the submodules
{Iκ
H(A) ⊆ O×μ(A)}H [where H ranges over the open subgroups of G], namely, as
the unique Ism-orbit of G-equivariant isomorphisms O×μ(G)∼ → O×μ(A) that maps
O×(G)H onto Iκ
H(A) for each open subgroup H ⊆ G. That is to say,
a ×μ-Kummer structure κ×μ on C may be thought of as — i.e., in the
sense that it determines and is uniquely determined by — the collection
of submodules {Iκ
H(A) ⊆ O×μ(A)}H [where H ranges over the open
subgroups of G].
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 155
Finally, weshallrefertoasa[×-, ×μ-]Kummer FrobenioidanyFrobenioidequipped
with a [×-, ×μ-]Kummer structure. We shall refer to as a split-[×-, ×μ-]Kummer
Frobenioid any split Frobenioid equipped with a [×-, ×μ-]Kummer structure.
(ii) Let
‡F⊢
= {‡F⊢
v }v∈V
be an F⊢-prime-strip; w ∈ Vbad. Write ‡D⊢ = {‡D⊢
v}v∈V for the D⊢-prime-
strip associated to ‡F⊢ [cf. [IUTchI], Remark 5.2.1, (i)]. Thus, ‡F⊢
w is a split
Frobenioid [cf. [IUTchI], Definition 5.2, (ii), (a); [IUTchI], Example 3.2, (v)], with
base category ‡D⊢
w. Let ‡A be a “universal covering pro-object” of ‡D⊢
w [cf. the
discussion of (i)]. Write ‡G def = Aut(‡A) [so ‡G is a profinite group isomorphic to
Gw]. Then the 2l-torsion subgroup μ2l(‡A) ⊆ O×(‡A) of the submonoid of units
O×(‡A) ⊆ O◃(‡A) of O◃(‡A), together with the images of the splittings with which
‡F⊢
w is equipped, generate a submonoid O⊥(‡A) ⊆ O◃(‡A), whose quotient by
μ2l(‡A) we denote by
O◃(‡A) ⊇ O⊥(‡A) O (‡A) def
= O⊥(‡A)/μ2l(‡A)
[so we have a natural isomorphism O◃(‡A)/O×(‡A)∼ → O (‡A)]. Write
O ×μ(‡A) def
= O (‡A) × O×μ(‡A)
for the direct product monoid. Thus, the monoids O◃(‡A), O⊥(‡A), O (‡A),
O×(‡A), O×μ(‡A), Oμ(‡A), and O ×μ(‡A) are all equipped with natural ‡G-
actions. Next, we consider the group-theoretic algorithms“G → (G O×(G))”
and “G → (G O×μ(G))” discussed in Example 1.8, (iii), (iv). If we apply the
first of these algorithms to ‡G, then it follows from Remark 1.11.1, (b), that there
exists a unique Z×-orbit of isomorphisms
‡κ⊢×
w : O×(‡G)∼ → O×(‡A)
of ind-topological modules equipped with ‡G-actions. Moreover, ‡κ⊢×
w induces an
Ism-orbit [cf. Example 1.8, (iv)] of isomorphisms
‡κ⊢×μ
w : O×μ(‡G)∼ → O×μ(‡A)
— i.e., by forming the quotient by “Oμ(−)”.
(iii) In the notation of (ii), the [rational function monoid determined by the
groupification of the] monoid with ‡G-action O ×μ(‡A), together with the divisor
monoid of [the underlying Frobenioid of] ‡F⊢
w, determines a “model Frobenioid” [cf.
[FrdI], Theorem 5.2, (ii)] equipped with a splitting, i.e., the splitting arising from
the definition of O ×μ(‡A) as a direct product. Thus, the ‡G-module obtained by
evaluating at ‡A the group of units “O×(−)” (respectively, the monoid “O◃(−)”)
associated to this Frobenioid may be naturally identified with O×μ(‡A) (respec-
tively, O ×μ(‡A)). In particular, the Ism-orbit of isomorphisms ‡κ⊢×μ
w determines
a ×μ-Kummer structure on this Frobenioid. We shall write
‡F⊢ ×μ
w
156 SHINICHI MOCHIZUKI
for the resulting split-Kummer Frobenioid and — by abuse of notation! —
‡F⊢
w
for the split-Kummer Frobenioid determined by the split Frobenioid ‡F⊢
w equipped
with the ×-Kummer structure determined by ‡κ⊢×
w . Here, we remark that the
primary justification for this abuse of notation lies in the uniqueness of ×-Kummer
structures discussed in (i) above.
(iv) Let ‡F⊢ be as in (ii); w ∈ Vgood Vnon. Thus, ‡F⊢
w is a split Frobenioid [cf.
[IUTchI], Definition 5.2, (ii), (a); [IUTchI], Example 3.3, (i)], with base category
‡D⊢
w. Let ‡A be a “universal covering pro-object” of ‡D⊢
w [cf. the discussion of
(i)]. Write ‡G def = Aut(‡A) [so ‡G is a profinite group isomorphic to Gw]. Then
the image of the splitting with which ‡F⊢
w is equipped determines a submonoid
O⊥(‡A) ⊆ O◃(‡A). Write O (‡A) def
= O⊥(‡A),
O ×μ(‡A) def
= O (‡A) × O×μ(‡A)
for the direct product monoid. Thus, the monoids O◃(‡A), O⊥(‡A), O (‡A),
O×(‡A), O×μ(‡A), Oμ(‡A), and O ×μ(‡A) are all equipped with natural ‡G-
actions. Next, we consider the group-theoretic algorithms“G → (G O×(G))”
and “G → (G O×μ(G))” discussed in Example 1.8, (iii), (iv). If we apply the
first of these algorithms to ‡G, then it follows from Remark 1.11.1, (b), that there
exists a unique Z×-orbit of isomorphisms
‡κ⊢×
w : O×(‡G)∼ → O×(‡A)
of ind-topological modules equipped with ‡G-actions. Moreover, ‡κ⊢×
w induces an
Ism-orbit [cf. Example 1.8, (iv)] of isomorphisms
‡κ⊢×μ
w : O×μ(‡G)∼ → O×μ(‡A)
— i.e., by forming the quotient by “Oμ(−)”. The [rational function monoid de-
termined by the groupification of the] monoid with ‡G-action O ×μ(‡A), together
with the divisor monoid of [the underlying Frobenioid of] ‡F⊢
w, determines a “model
Frobenioid”[cf. [FrdI],Theorem5.2, (ii)]equippedwithasplitting, i.e., thesplitting
arising from the definition of O ×μ(‡A) as a direct product. Thus, the ‡G-module
obtained by evaluating at ‡A the group of units “O×(−)” (respectively, the monoid
“O◃(−)”) associated to this Frobenioid may be naturally identified with O×μ(‡A)
(respectively, O ×μ(‡A)). In particular, the Ism-orbit of isomorphisms ‡κ⊢×μ
w de-
termines a ×μ-Kummer structure on this Frobenioid. We shall write
‡F⊢ ×μ
w
for the resulting split-Kummer Frobenioid and — by abuse of notation! [cf. the
discussion of (iii) above] —
‡F⊢
w
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 157
for the split-Kummer Frobenioid determined by the split Frobenioid ‡F⊢
w equipped
with the ×-Kummer structure determined by ‡κ⊢×
w.
(v) Let ‡F⊢ be as in (ii); w ∈ Varc. Then we shall write
‡F⊢ ×μ
w
for the collection of data obtained by replacing the split Frobenioid that appears in
the collection of data ‡F⊢
w [cf. [IUTchI], Definition 5.2, (ii), (b); [IUTchI], Example
3.4, (ii)] by the inductive system, indexed by any [“multiplicatively”] cofinal subset
of the multiplicative monoid N≥1, of split Frobenioids obtained [in the evident
fashion] from ‡F⊢
w by forming the quotients by the N-torsion, for N ∈ N≥1. Here,
weidentify[intheevidentfashion]theinductivesystemsarisingfromdistinctcofinal
subsets of N≥1. Thus, [cf. the notation of (i)] the units of the split Frobenioids of
this inductive system give rise to an inductive system
... O×μN (A)... O×μN·N′ (A)...
[where N,N′ ∈ N≥1]. Now recall that ‡D⊢
w is an object of the category TM⊢ [cf.
[IUTchI], Definition 4.1, (iii), (b)]. In particular, the units (‡D⊢
w)× of this object of
TM⊢ form a topological group [noncanonically isomorphic to S1], which we think of
as being related to the above inductive system of units via a system of compatible
surjections
(‡D⊢
w)× O×μN (A)
[i.e., wherethekernelofthedisplayedsurjectionisthesubgroupofN-torsion]. This
system of compatible surjections is well-defined up to an indeterminacy given by
composition with the unique nontrivial automorphism of (‡D⊢
w)×. When considered
uptothisindeterminacy, thissystemofcompatiblesurjectionsmaybethoughtofas
asortofKummer structureon‡F⊢ ×μ
w [whichmaybealgorithmicallyreconstructed
from the collection of data ‡F⊢ ×μ
w ].
(vi) Write
‡F⊢ ×μ = {‡F⊢ ×μ
v }v∈V
for the collection of data indexed by V obtained as follows: (a) if v ∈ Vbad, then
we take ‡F⊢ ×μ
v to be the split-Kummer Frobenioid constructed in (iii); (b) if v ∈
Vgood Vnon, then we take ‡F⊢ ×μ
v to be the split-Kummer Frobenioid constructed
in (iv); (c) if v ∈ Varc, then we take ‡F⊢ ×μ
v to be the collection of data constructed
in (v). Moreover, by replacing the various split Frobenioids of ‡F⊢ (respectively,
‡F⊢ ×μ) with the split Frobenioids — i.e., equipped with trivial splittings! —
obtainedbyconsideringthesubcategories[oftheunderlyingcategoriesassociatedto
these Frobenioids] determined by the isometries [i.e., roughly speaking, the “units”
— cf. [FrdI], Theorem 5.1, (iii), in the case of v ∈ Vnon; [FrdII], Example 3.3, (iii),
in the case of v ∈ Varc], one obtains a collection of data
‡F⊢×
= {‡F⊢×
v }v∈V (respectively, ‡F⊢×μ = {‡F⊢×μ
v }v∈V)
indexed by V. Thus, for each v ∈ Vnon
,
(respectively, split-×μ-) Kummer Frobenioid.
‡F⊢×
v (respectively, ‡F⊢×μ
v ) is a split-×-
158 SHINICHI MOCHIZUKI
(vii) Let ⊢ ∈ { ⊢×, ⊢×μ, ⊢ ×μ }. Then we define an F⊢ -prime-strip
to be a collection of data
∗F⊢
= {∗F⊢
v }v∈V
such that for each v ∈ V,
∗F⊢
v is a collection of data that is isomorphic to ‡F⊢
v
[cf. (vi)]. A morphism of F⊢ -prime-strips is defined to be a collection of isomor-
phisms, indexed by V, between the various constituent objects of the prime-strips
[cf. [IUTchI], Definition 5.2, (iii)].
(viii) We define an F ×μ-prime-strip to be a collection of data
∗F ×μ = (∗C , Prime(∗C )∼
→ V,
∗F⊢ ×μ
, {∗ρv}v∈V)
satisfying the conditions (a), (b), (c), (d), (e), (f) of [IUTchI], Definition 5.2, (iv),
for an F -prime-strip, where the portion of the collection of data constituted by
an F⊢-prime-strip is replaced by an F⊢ ×μ-prime-strip. Thus, relative to the
notation of the above display [cf. also (ii), (iii)], the generators of the monoids
“O (−)” [each of which is abstractly isomorphic to N] of the data at v ∈ Vbad (̸=
∅) [cf. [IUTchI], Definition 3.1, (b)] of∗F⊢ ×μ = {∗F⊢ ×μ
w }w∈V, together with
the {∗ρw}w∈V, determine a well-defined object, up to isomorphism, of the global
realified Frobenioid ∗C of negative “arithmetic degree” [cf. [FrdI], Example 6.3;
[FrdI], Theorem 6.4, (i), (ii)], which we refer to as the pilot object associated to the
F ×μ-prime-strip∗F ×μ. A morphism of F ×μ-prime-strips is defined to be
an isomorphism between collections of data as discussed above.
We conclude the present paper with the following two results, which may be
thought of as enhanced versions of [IUTchI], Corollaries 3.7, 3.8, 3.9 — i.e., versions
that reflect the various enhancements made to the theory in [IUTchI], §4, §5, §6,
as well as in the present paper.
Corollary 4.10. (Frobenius-pictures of Θ±ellNF-Hodge Theaters) Fix
a collection of initial Θ-data (F/F, XF, l, CK, V, Vbad
mod, ϵ) as in [IUTchI],
Definition 3.1. Let
†HT Θ±ellNF
; ‡HT Θ±ellNF
be Θ±ellNF-Hodge theaters [relative to the given initial Θ-data] — cf. [IUTchI],
Definition 6.13, (i). Write †HT D-Θ±ellNF
,
‡HT D-Θ±ellNF for the associated D-
Θ±ellNF-Hodge theaters — cf. [IUTchI], Definition 6.13, (ii). Then:
(i) (Constant Prime-Strips) Let us apply the constructions of Corollary
4.6, (i), (iii), to the underlying Θ±ell-Hodge theater of †HT Θ±ellNF. Then, for each
t ∈ LabCusp±(†D≻), the collection of data Ψcns(†F≻)t determines, in a natural
way, an F-prime-strip [cf. Remark 4.6.2, (i)]. Let us identify the collections of
data
Ψcns(†F≻)0 and Ψcns(†F≻)⟨Fl ⟩
via the isomorphism of the second display of Corollary 4.6, (iii), and denote by
†F△ = (†C△, Prime(†C△)∼
→ V,
†F⊢
△, {†ρ△,v}v∈V)
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 159
the resulting F -prime-strip determined by the constructions discussed in [IUTchI],
Remark 5.2.1, (ii) [which, as is easily verified, are compatible with the F ±
l-
symmetrizing isomorphisms of Corollary 4.6, (iii)]. Thus, [it follows imme-
diately from the constructions involved that] one has a natural identification
isomorphism of F -prime-strips †F△
∼
→ †Fmod between †F△ and the collec-
tion of data †Fmod associated to the underlying Θ-Hodge theater of †HT Θ±ellNF [cf.
[IUTchI], Definition 3.6, (c)] — cf. the discussion of the assignment
“ 0, ≻ → > ”
in Remark 3.8.2, (ii).
(ii) (Theta and Gaussian Prime-Strips) Let us apply the constructions
of Corollary 4.6, (iv), (v), to the underlying Θ-bridge and Θ±ell-Hodge theater of
†HT Θ±ellNF. Then the collection of data ΨFenv(†HT Θ) [cf. Corollary 4.6, (iv)],
the global realified Frobenioid †Cenv
def
= Cenv(†HT Θ) [cf. Corollary 4.6, (v)], and the
∼
local isomorphisms ΦCenv(†HT Θ),v
→ ΨFenv(†HT Θ)R
v for v ∈ V [cf. Corollary 4.6,
(v)] give rise, in a natural fashion, to an F -prime-strip
†Fenv = (†Cenv, Prime(†Cenv)∼
→ V,
†F⊢
env, {†ρenv,v}v∈V)
[so, in particular, †F⊢
env is the F⊢-prime-strip determined by ΨFenv(†HT Θ) — cf.
Remark 4.6.2, (i); Remark 4.10.1 below]. Thus, [it follows immediately from the
constructions involved that] there is a natural identification isomorphism of
F -prime-strips †Fenv
∼
→ †Ftht between †Fenv and the collection of data †Ftht as-
sociated to the underlying Θ-Hodge theater of †HT Θ±ellNF [cf. [IUTchI], Definition
3.6, (c)]. In a similar vein, the collection of data ΨFgau(†HT Θ) [cf. Corollary
4.6, (iv)], the global realified Frobenioid †Cgau
def
= Cgau(†HT Θ) [cf. Corollary 4.6,
(v)], and the local isomorphisms ΦCgau(†HT Θ),v
∼
→ ΨFgau(†HT Θ)R
v for v ∈ V [cf.
Corollary 4.6, (v)] give rise, in a natural fashion, to an F -prime-strip
†Fgau = (†Cgau, Prime(†Cgau)∼
→ V,
†F⊢
gau, {†ρgau,v}v∈V)
[so, in particular, †F⊢
gau is the F⊢-prime-strip determined by ΨFgau(†HT Θ) — cf.
Remark 4.6.2, (i); Remark 4.10.1 below]. Finally, the evaluation isomorphisms of
Corollary 4.6, (iv), (v), determine an evaluation isomorphism
†Fenv
∼
→ †Fgau
of F -prime-strips.
(iii) (Θ×μ- and Θ×μ
gau-Links) Write ‡F ×μ
△ (respectively, †F ×μ
env ; †F ×μ
gau )
for the F ×μ-prime-strip associated to the F -prime-strip ‡F△ (respectively, †Fenv;
†Fgau) [cf. Definition 4.9, (viii); the functorial algorithm described in Definition
4.9, (vi)]. Then the functoriality of this algorithm induces maps
IsomF (†Fenv,
‡F△) → IsomF ×μ (†F ×μ
env ,
‡F ×μ
△ )
IsomF (†Fgau,
‡F△) → IsomF ×μ (†F ×μ
gau ,
‡F ×μ
△ )
160 SHINICHI MOCHIZUKI
from [nonempty!] sets of isomorphisms of F -prime-strips to [nonempty!] sets
of isomorphisms of F ×μ-prime-strips. Here, the second map may be regarded
as being obtained from the first map via composition [in the case of the domain
“IsomF (−
,−)”] with the evaluation isomorphism †Fenv
∼
→ †Fgau of (ii) and
composition [in the case of the codomain “IsomF ×μ (−
,−)”] with the isomorphism
†F ×μ
∼
env
→ †F ×μ
gau functorially obtained from this isomorphism of (ii). We shall
refer to the full poly-isomorphism †F ×μ
∼
env
→ ‡F ×μ
△ as the Θ×μ-link
†HT Θ±ellNF Θ×μ
−→ ‡HT Θ±ellNF
[cf. the “Θ-link” of [IUTchI], Corollary 3.7, (i)] from †HT Θ±ellNF to ‡HT Θ±ellNF
,
and to the full poly-isomorphism †F ×μ
∼
→ ‡F ×μ
gau
△ as the Θ×μ
gau-link
†HT Θ±ellNF Θ×μ
gau −→ ‡HT Θ±ellNF
from †HT Θ±ellNF to ‡HT Θ±ellNF
.
(iv) (Coric F⊢×μ-Prime-Strips) The definition of the unit portion of the
theta and Gaussian monoids involved [cf. Corollary 3.5, (ii); Corollary 3.6,
(ii); Proposition 4.1, (iv); Proposition 4.2, (iv); Proposition 4.3, (iv); Proposition
4.4, (iv)] gives rise to natural isomorphisms
†F⊢×μ
△
∼
→ †F⊢×μ
env
∼
→ †F⊢×μ
gau
— where we write †F⊢×μ
△ ,
†F⊢×μ
env ,
†F⊢×μ
gau for the F⊢×μ-prime-strips associated to
the F⊢-prime-strips †F⊢
△,
†F⊢
env,
†F⊢
gau, respectively [cf. the functorial algorithm
described in Definition 4.9, (vi)]. Moreover, by composing these natural isomor-
phisms with the poly-isomorphisms induced on the respective F⊢×μ-prime-strips by
the Θ×μ- and Θ×μ
gau-links of (iii), one obtains a poly-isomorphism
†F⊢×μ
△
∼
→ ‡F⊢×μ
△
which coincides with the full poly-isomorphism between these two F⊢×μ-prime-
strips — that is to say, “(−)F⊢×μ
△ ” is an invariant of both the Θ×μ- and Θ×μ
gau-links.
Finally, this full poly-isomorphism induces [cf. Definition 4.9, (vii); [IUTchI],
Remark 5.2.1, (i)] the full poly-isomorphism
†D⊢
△
∼
→ ‡D⊢
△
between the associated D⊢-prime-strips; we shall refer to this poly-isomorphism as
the D-Θ±ellNF-link from †HT D-Θ±ellNF to ‡HT D-Θ±ellNF
.
(v) (Coric Global Realified Frobenioids) The full poly-isomorphism †D⊢
△
∼
→ ‡D⊢
△ of (iv) induces [cf. Corollary 4.5, (ii)] an isomorphism of collections of
data
(D (†D⊢
△), Prime(D (†D⊢
△))∼
→ V, {†ρD ,v}v∈V)
∼
→ (D (‡D⊢
△), Prime(D (‡D⊢
△))∼
→ V, {‡ρD ,v}v∈V)
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 161
— i.e., consisting of a Frobenioid, a bijection, and a collection of isomorphisms of
topological monoids indexed by V. Moreover, this isomorphism of collections of data
is compatible, relative to the Θ×μ- and Θ×μ
gau-links of (iii), with the R>0-orbits
of the isomorphisms of collections of data
(†C△, Prime(†C△)∼
→ V, {†ρ△,v}v∈V)
∼
→ (D (†D⊢
△), Prime(D (†D⊢
△))∼
→ V, {†ρD ,v}v∈V)
(‡C△, Prime(‡C△)∼
→ V, {‡ρ△,v}v∈V)
∼
→ (D (‡D⊢
△), Prime(D (‡D⊢
△))∼
→ V, {‡ρD ,v}v∈V)
obtained by applying the functorial algorithm discussed in the final portion of Corol-
lary 4.6, (ii). Here, the “R>0-orbits” are defined relative to the natural R>0-
actions on the Frobenioids involved obtained by multiplying the “arithmetic de-
grees” by a given element ∈ R>0 [cf. [FrdI], Example 6.3; [FrdI], Theorem 6.4, (ii);
[IUTchI], Remark 3.1.5].
(vi) (Frobenius-pictures) Let {nHT Θ±ellNF}n∈Z be a collection of distinct
Θ±ellNF-Hodge theaters indexed by the integers. Then by applying the Θ×μ- and
Θ×μ
gau-links of (iii), we obtain infinite chains
Θ×μ
...
−→ (n−1)HT Θ±ellNF Θ×μ
−→ nHT Θ±ellNF Θ×μ
−→ (n+1)HT Θ±ellNF Θ×μ
−→...
Θ×μ
...
gau −→ (n−1)HT Θ±ellNF Θ×μ
gau −→ nHT Θ±ellNF Θ×μ
gau −→ (n+1)HT Θ±ellNF Θ×μ
gau −→...
of Θ×μ-/Θ×μ
gau-linked Θ±ellNF-Hodge theaters. Either of these infinite chains
may be represented symbolically as an oriented graph⃗
Γ [cf. [AbsTopIII], §0]
... → • → • → • →...
— i.e., where the arrows correspond to either the “ Θ×μ
Θ×μ
−→ ’s” or the “
gau −→ ’s”, and
the “•’s” correspond to the “nHT Θ±ellNF”. This oriented graph⃗
Γ admits a natural
action by Z — i.e., a translation symmetry — but it does not admit arbitrary
permutation symmetries. For instance,⃗
Γ does not admit an automorphism that
switches two adjacent vertices, but leaves the remaining vertices fixed — cf. the
discussion of [IUTchI], Corollary 3.8; [IUTchI], Remark 3.8.1.
Proof. The various assertions of Corollary 4.10 follow immediately from the defi-
nitions and the references quoted in the statements of these assertions. ⃝
Remark 4.10.1. Strictly speaking [cf. Remark 4.6.2, (i)], the F⊢-prime-strips
constructed, in Corollary 4.10, (ii), from the theta and Gaussian monoids of Corol-
lary 4.6, (iv), are only well-defined up to an indeterminacy, at the v ∈ Vbad, relative
to automorphisms of the split Frobenioid at such v ∈ Vbad that induce the iden-
tity automorphism on the associated F⊢×-prime-strip. On the other hand, such
162 SHINICHI MOCHIZUKI
indeterminacies may, in essence, be ignored, since they are “absorbed” in the full
poly-isomorphisms that appear in the Θ×μ- and Θ×μ
gau-links of Corollary 4.10, (iii).
Remark 4.10.2.
(i) Although both the Θ×μ- and Θ×μ
gau-links are treated, in essence, on an
equal footing in Corollary 4.10, in the remainder of the present series of papers, we
shall ultimately mainly be interested in [a further enhanced version of] the Θ×μ
gau-
link. On the other hand, the significance of the Θ×μ-link lies in the fact that it is
precisely by thinking of [a further enhanced version of] the Θ×μ
gau-link as an object
that is constructed as the composite of the Θ×μ-link with the operation of Galois
evaluation that one may establish the crucial multiradiality properties discussed
in [IUTchIII], Theorem 3.11.
(ii) At v ∈ Vbad, the Θ×μ-link may be thought of as a sort of equivalence
between the split theta monoids of Proposition 3.1, (i) [cf. also Corollary 1.12, (ii)]
and certain submonoids of the constant monoids of Proposition 3.1, (ii), equipped
with the splittings that arise from the q-parameter “q
” [cf. the discussion of “τ⊢
”
v
v
in [IUTchI], Example 3.2, (iv)]. On the other hand, it is important to note in this
context that unlike the case with the splittings that occur in the case of the theta
monoids, the splittings that occur in the case of the constant monoids do not arise
from the operation of Galois evaluation — i.e., from a splitting “H → Gv” at the
level of Galois groups of some surjection Gv H. In particular, the splittings in
the case of the constant monoids do not admit a natural multiradial formulation
[cf. Remark 1.11.5; Proposition 3.4, (ii)], as in the case of the theta monoids [cf.
Corollary 1.12, (iii)], that allows one to decouple the monoids into “purely radial”
and “purely coric” components [cf. discussion of Remarks 1.11.4, (i); 1.12.2, (vi)].
Remark 4.10.3.
(i) The “coricity of F⊢×μ-prime-strips”
†F⊢×μ
△
∼
→ ‡F⊢×μ
△
discussed in Corollary 4.10, (iv), amounts, in essence, to the “coricity of D⊢-prime-
strips” †D⊢
∼
→ ‡D⊢
△
△ [cf. Corollary 4.10, (iv)], together with the “coricity of
[various quotients by torsion of] the units O×(−)” of the Frobenioids involved —
cf. [IUTchI], Corollary 3.7, (ii), (iii). In [IUTchIII], this coricity of the units
will play a central role when we apply the theory of the log-wall [cf. [AbsTopIII]].
In particular, this coricity of the units will allow us to compare volumes on either
side of the Θ×μ-, Θ×μ
gau-links.
(ii) Unlike the units [cf. the discussion of (i)!], the “divisor monoid”, or “value
group”, portion of the Frobenioids involved is by no means preserved by the Θ×μ-,
Θ×μ
gau-links! Indeed, this “value group” portion of the Θ×μ-, Θ×μ
gau-links may be
thought of as a sort of “Frobenius morphism” — cf. the discussion of Remark
3.6.2, (iii), as well as Remark 4.11.1 below. Alternatively, from the point of view
of the analogy between [complex or p-adic] Teichm¨ uller theory and the theory of
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 163
the present series of papers, this portion of the Θ×μ-, Θ×μ
gau-links may be thought
of as a sort of Teichm¨ uller deformation [cf. the discussion of [IUTchI], Remark
3.9.3, (ii)]. Indeed, the computation of the “volume distortion” arising from this
“arithmetic Teichm¨ uller deformation” may, in some sense, be regarded as the
ultimate goal of the present series of papers.
(iii) In the context of the discussion of (ii), it is interesting to note that if one
restricts the value group portion of the Θ×μ
gau-link — i.e.,
q
v
→ qj2
v 1≤j≤l
[cf. Remark 3.6.2, (iii)] — to the label j = 1, then the resulting correspondence
q
v
→ q
v
may be naturally identified with the “identity” — cf. the discussion of Remark
3.6.2, (iii). Put another way, the restriction to the label j = 1 of the Gaussian
distribution may be identified, for instance at the level of realifications, with the
pivotal distribution discussed in [IUTchI], Example 5.4, (vii). On the other hand, in
this context, it is important to observe that the operation of restriction to various
proper subsets of the set of all labels |Fl| fails, in general, to be compatible with the
crucial F ±
l- and Fl -symmetries of Corollaries 4.5, (iii); 4.6, (iii); 4.7, (ii); 4.8,
(ii) [cf. also the discussion of Remark 2.6.3].
nHT D-Θ±ellNF
...
|...
n
′HT D-Θ±ellNF
— (−)D⊢
△
—
n
′′HT D-Θ±ellNF
...
|
...
n
′′′HT D-Θ±ellNF
Fig. 4.3:
´
Etale-picture of D-Θ±ellNF-Hodge Theaters
´
Corollary 4.11. (
Etale-pictures of Base-Θ±ellNF-Hodge Theaters) Sup-
pose that we are in the situation of Corollary 4.10, (vi).
(i) Write
...
D
−→ nHT D-Θ±ellNF D
−→ (n+1)HT D-Θ±ellNF D
−→...
164 SHINICHI MOCHIZUKI
— where n ∈ Z — for the infinite chain of D-Θ±ellNF-linked D-Θ±ellNF-
Hodge theaters [cf. Corollary 4.10, (iv), (vi)] induced by either of the infinite
chains of Corollary 4.10, (vi). Then this infinite chain induces a chain of full
poly-isomorphisms
...
∼
→ nD⊢
△
∼
→ (n+1)D⊢
△
∼
→...
[cf. Corollary 4.10, (iv)]. That is to say, “(−)D⊢
△” forms a constant invariant
[cf. the discussion of [IUTchI], Remark 3.8.1, (ii)] — i.e., a mono-analytic core
[cf. the situation discussed in [IUTchI], Remark 3.9.1] — of the above infinite
chain.
(ii) If we regard each of the D-Θ±ellNF-Hodge theaters of the chain of (i) as a
spoke emanating from the mono-analytic core “(−)D⊢
△” discussed in (i), then we
obtain a diagram — i.e., an´ etale-picture of D-Θ±ellNF-Hodge theaters — as
in Fig. 4.3 above [cf. the situation discussed in [IUTchI], Corollaries 4.12, 6.10].
Thus, each spoke may be thought of as a distinct “arithmetic holomorphic
structure” on the mono-analytic core. Finally, [cf. the situation discussed in
[IUTchI], Corollaries 4.12, 6.10] this diagram satisfies the important property of
admitting arbitrary permutation symmetries among the spokes [i.e., the labels
n ∈ Z of the D-Θ±ellNF-Hodge theaters].
(iii) The constructions of (i) and (ii) are compatible, in the evident sense,
with the constructions of [IUTchI], Corollaries 4.12, 6.10, relative to the natural
identification isomorphisms (−)D⊢
∼
→ (−)D⊢
△
> [cf. Corollary 4.10, (i); the
discussion preceding [IUTchI], Example 5.4] and the operation of passing to the
underlying D-ΘNF- [in the case of [IUTchI], Corollary 4.12] and D-Θ±ell
-Hodge
theaters [in the case of [IUTchI], Corollary 6.10].
Proof. The various assertions of Corollary 4.11 follow immediately from the defi-
nitions and the references quoted in the statements of these assertions. ⃝
Remark 4.11.1. The Θ×μ
gau-link of Corollary 4.10, (iii), may be thought of,
roughly, as a sort of transformation
q → q
12
.
.
(l )2
.
—cf. thediscussionofRemark3.6.2,(iii). Fromthispointofview,theinfinitechain
of the Frobenius-picture discussed in Corollary 4.10, (vi), may be represented as
an infinite iteration
q →
q
12
.
(l )2
.
.
12
.
.
(l )2
.
···
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 165
of this transformation. By contrast, the associated´ etale-picture discussed in
Corollary 4.11 corresponds to a sort of commutativity involving these “theta expo-
nents”
q → q
12
.
.
(l )2
.
·
12
.
.
(l )2
.
·
12
.
.
(l )2
.
···
— cf. the “arbitrary permutation symmetries” discussed in Corollary 4.11, (ii). In
this context, it is useful to recall the analogy between the classical Gaussian in-
tegral and the theory of the present series of papers [cf. Remark 1.12.5] — an anal-
ogy in which the “order-conscious” Frobenius-picture corresponds to the carte-
sian coordinate representation of the Gaussian integral, while the “permutation-
symmetric”´ etale-picture corresponds to the polar coordinate representation of
the Gaussian integral. Finally, from the point of view of the discussion of Remark
4.7.4, the l-torsion that occurs as the index set of the various “qj2’s” that appear
in the Gaussian monoid of each Θ±ellNF-Hodge theater may be thought of as a
sort of multiradial combinatorial representation of the distinct “arithmetic
holomorphic structures” corresponding to the various Θ±ellNF-Hodge theaters.
Remark 4.11.2. in the present series of papers.
At this point, we pause to review the theory developed so far
(i) The notion of a Θ±ellNF-Hodge theater [cf. [IUTchI], Definition 6.13, (i)] is
intended as a model of conventional scheme-theoretic arithmetic geometry
— i.e., more precisely, of the conventional scheme-theoretic arithmetic geometry
surrounding the theta function at primes of bad reduction ∈ Vbad of the elliptic
curveoveranumberfieldunderconsideration. Atamoretechnicallevel, aΘ±ellNF-
Hodge theater may be thought of as an apparatus that allows one to construct a
sort of bridge between the number field and theta functions [at v ∈ Vbad]
under consideration. From a more concrete point of view, this bridge is realized by
the Gaussian distribution — i.e., a globalized version of the theta values
qj2
v 1≤j≤l
at l-torsion points [cf. Remark 3.6.2, (iii)]. Here, we remark that the term “Gauss-
ian distribution” is intended as an intuitive expression that includes the more tech-
nical notions of “Gaussian monoids” and “Gaussian Frobenioids”. The Gaussian
distribution also plays the crucial role of allowing the construction of the [non-
scheme/ring-theoretic!] Θ×μ
gau-link between distinct Θ±ellNF-Hodge theaters [cf.
Corollary 4.10, (iii)] — i.e., between distinct models of conventional scheme-
theoretic arithmetic geometry.
(ii) Within a single Θ±ellNF-Hodge theater, the theory of´ etale and Frobenioid-
theoretic theta functions developed in [EtTh] is applied to construct a single con-
nected geometric “Kummer theory-compatible theater for evaluation of the theta
function”, whose´ etale-theoretic realization admits a multiradial formulation [cf.
the theory of §1, especially Corollary 1.12], and whose connectedness allows one
to establish conjugate synchronization [cf. the discussion of Remark 2.6.1]
166 SHINICHI MOCHIZUKI
between the various copies of the absolute Galois group of the base field at the
various l-torsion points at which the theta function is evaluated. Moreover, this
conjugate synchronization satisfies the crucial property of compatibility with the
F ±
l -symmetry [cf. the discussion of Remark 3.5.2, as well as Corollaries 4.5,
(iii); 4.6, (iii)] of the underlying D-Θell-bridge [cf. [IUTchI], Proposition 6.8, (i)] of
the Θ±ellNF-Hodge theater under consideration. Conjugate synchronization plays
an essential role in establishing the coricity of the units [cf. Corollary 4.10,
(iv)] in a fashion which is compatible with both the´ etale-theoretic — i.e., “an-
abelian” — and abstract monoid/Frobenioid-theoretic — i.e., “post-anabelian”
— representations of the Gaussian monoids [cf. the discussion of Remark 3.8.3].
Here, we recall that the “post-anabelian” representation of the Gaussian monoids
is necessary to construct the Θ×μ
gau-link of Corollary 4.10, (iii) [cf. Remarks 3.6.2,
(ii); 3.8.3, (i)]. On the other hand, the “anabelian” representation of the Gaussian
monoids will play an essential role when we apply the theory of the log-wall [cf.
[AbsTopIII]] in [IUTchIII] [cf. Remark 3.8.3, (ii)]. Another important aspect of the
theory of Gaussian distibutions, at v ∈ Vbad, is the canonical splittings of the
monoids involved into “unit” and “value group” components. These splittings
may be thought of, in the context of the Θ×μ
gau-link, as corresponding to the “non-
deformed” [cf. the “coricity of the units”] and “Teichm¨ uller-dilated” [cf. the
“value group” portion of the Gaussian distribution] real dimensions that appear
in classical complex Teichm¨ uller theory [cf. the discussion of Remark 4.10.3, (i),
(ii)]. Finally, these splittings will play a crucial role in the theory of log-shells [cf.
[AbsTopIII]], which we shall apply in [IUTchIII].
(iii) By contrast, the number fields that appear in the underlying ΘNF-
Hodge theater of the Θ±ellNF-Hodge theater under consideration [cf. the theory of
[IUTchI], §5] will ultimately, in [IUTchIII], in the context of log-shells, play the
role of relating — via the ring structure of these number fields — -line bundles
[i.e., “id` elic” or “Frobenioid-theoretic” line bundles] to“ -line bundles” [i.e., line
bundles thought of as modules] — cf. the discussion of Remark 4.7.2. Such rela-
tionships are only possible if one considers all of the primes of the number fields
involved [cf. [AbsTopIII], Remark 5.10.2, (iv)]. Constructions associated to these
number fields satisfy the property of being compatible with the Fl -symmetry [cf.
[IUTchI], Proposition 4.9, (i)] of the underlying NF-bridge of the Θ±ellNF-Hodge
theater under consideration. Unlike the F ±
l -symmetry discussed in (ii), which is
combinatorially uniradial in nature and may be thought of, in the context of the
splittings discussed in (ii), as being associated with the “units”, the Fl -symmetry
is combinatorially multiradial in nature and may be thought of, in the context of
the splittings discussed in (ii), as being associated with the “value groups” [cf. the
discussion of Remarks 4.7.3, 4.7.4, 4.7.5]. On the other hand, [cf. the discussion
of (ii)] the F ±
l -symmetry satisfies the crucial property of being compatible with
conjugate synchronization — a property which may only be established after
one isolates the prime-strips under consideration from the conjugacy indetermi-
nacies inherent in the global structure of the absolute Galois group of a number
field [cf. Remark 4.7.2]. Put another way, conjugate synchronization may only be
established once the prime-strips under consideration are treated as objects which
are free of any combinatorial constraints arising from the “prime-trees” asso-
ciated to a number field [cf. the discussion of [IUTchI], Remark 4.3.1]. On the other
hand, one important property shared by both the F ±
l - and Fl -symmetries is the
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 167
connectedness of the global objects that appear in the [Θell-/NF-bridges of] these
symmetries. This connectedness plays an essential role in the bookkeeping opera-
tions involving the labels of the evaluation points [cf. the discussion of Remarks
3.5.2 and 4.5.3, (iii), as well as [IUTchI], Remark 4.9.2, (i)]. In particular, such
bookkeeping operations cannot be implemented if, for instance, instead of working
with a global number field, one attempts to take as one’s “global objects” formal
products of the local objects at the various primes of the number field under con-
sideration [cf. the discussion of [AbsTopIII], Remark 3.7.6, (v)]. Finally, we recall
that the essential role played by these “global bookkeeping operations” gives rise,
in light of the profinite nature of the global geometric ´ etale fundamental groups
involved, to a situation in which one must apply the “complements on tempered
coverings” developed in [IUTchI], §2 [cf. Remark 4.5.3, (iii)].
(iv) One way to summarize the above discussion is as follows. The bridge
constituted by the Gaussian distribution of a Θ±ellNF-Hodge theater between theta
functionsandnumber fieldsmaybethoughtofasbeingconstructedbydismantling
those aspects of the “characteristic topography” of the theta functions and
number fields involved that constitute an obstruction to relating theta functions to
number fields. In the case of theta functions, the main obstruction to constructing
such a link to the number field under consideration is constituted by the geometric
dimension of the tempered coverings of elliptic curves [at v ∈ Vbad] on which the
theta functions are defined. This obstruction is resolved by means of the operation
of evaluation at the l-torsion points. Thus, from the point of view of the scheme-
theoretic Hodge-Arakelov theory of [HASurI], [HASurII], one may think of these
l-torsion points as a sort of “rough finite approximation” of the tempered coverings
of elliptic curves under consideration [cf. the discussion of [HASurI], §1.3.4]. By
contrast, in the case of number fields, the main obstruction to constructing such
a link to the theta functions under consideration is the “prime-trees” arising
from the global structure of the number field, which give rise to the conjugacy
indeterminacies that obstruct the establishment of conjugate synchronization
[cf. the discussion of (iii) above]. This obstruction is resolved by dismantling the
global prime-tree structure of the number fields involved by working with various
prime-strips labeled by elements ∈ Fl [cf. the discussion of [IUTchI], Remark
4.3.1]. Thus, one may think of these collections of prime-strips labeled by elements
∈ Fl as “rough finite approximations” of the infinite prime-trees associated to
the number fields involved. At a more combinatorial level [cf. the discussion
of Remark 4.7.5], this dismantling process may be thought of as the process of
dismantling the ring structure of Fl — which we think of as a “rough finite
approximation” of Z [cf. [IUTchI], Remark 6.12.3, (i)] — into its additive and
multiplicative components, which correspond, respectively, to the F ±
l- and Fl-
symmetries.
Remark 4.11.3. InthecontextofthediscussionofRemark4.11.2, itisinteresting
to observe that, whereas, from the point of view of the combinatorics of the F ±
l-
and Fl -symmetries, one has correspondences
Θell ←→ , NF ←→
— i.e., the Θell-bridge corresponds to the additive F ±
l -symmetry, while the NF-
bridgecorrespondstothemultiplicativeFl -symmetry—atthelevelofline bundles,
168 SHINICHI MOCHIZUKI
one has correspondences
Θell ←→ , NF ←→
— i.e., the arithmetic line bundles under consideration are treated multiplicatively,
via monoids or Frobenioids, in the context of the Θell-bridge, while the equivalence
of such -line bundles with -line bundles may only be realized in the context of
the global ring structure of the number fields associated, via the theory of [IUTchI],
§5, to the NF-bridge. This “juggling of and ” is reminiscent of the theory of
the log-wall developed in [AbsTopIII] [cf., e.g., the discussion of [AbsTopIII], §I3]
and, indeed, may be thought of as a sort of combinatorial counterpart to the
“juggling of and ” that occurs in the theory of the log-wall.
Remark 4.11.4.
(i) From the point of view of scheme-theoretic Hodge-Arakelov theory, the l-
torsion points of an elliptic curve may be thought of as a “rough finite approxi-
mation” of the two real dimensions of the underlying real analytic manifold of a
one-dimensional complex torus [cf. the discussion of [HASurI], §1.3.4]. In scheme-
theoreticHodge-Arakelovtheory,oneconsidersspacesoffunctionsonthesel-torsion
points. The two dimensions mentioned above then correspond to a “holomorphic
dimension” and a “one-dimensional deformation of this holomorphic dimension”
[cf. the discussion of [HASurI], §1.4.2]. In the context of the theory of the present
series of papers, we work, in eﬀect, with an elliptic curve which is isogenous to
the given elliptic curve via an isogeny of degree l — i.e., with “X” as opposed to
“X” — so that we may neglect the “holomorphic dimension” mentioned above and
concentrate instead on the deformations of this “holomorphic dimension” [cf. the
discussion of the Introduction to [EtTh]]. In particular, the various possible values
at the various l-torsion points at which the theta function is evaluated in the theory
of the present series of papers may be thought of as various possible deformations
of the holomorphic structure, while the specific values of the theta function may be
thought of as a specific deformation of the holomorphic structure. Here, we note
that the parameter “0 ̸= t ∈ LabCusp±(−)” that indexes these values — which,
like the tangent space to the original elliptic curve, is linear which respect to the
group structure of the elliptic curve — descends naturally [especially in the context
of ΘNF-Hodge theater!] to the parameter “j ∈ Fl ” — which may be thought of as
the “square (F×
l )2” of F×
l , hence, like the square of the tangent space of the elliptic
curve, which is naturally isomorphic to the tangent space to the moduli space of
elliptic curves at the point determined by the elliptic curve in question, is quadratic
in its dependence on the linear group structure of the elliptic curve. Finally, this
point of view concerning the values of the theta function is reminiscent of the point
of view of Remark 3.6.2, (iii), in which we observe that, in the context of the Θ×μ
gau-
link, these values of the theta function may be thought of as a sort of “deformation
between the identity and a Frobenius morphism”. The theta function involved may
then be thought of as a sort of continuous version [i.e., as opposed to a “rough
finite approximation”] of such a deformation.
(ii) From the point of view of the analogy between the theory of the present
series of papers and p-adic Teichm¨ uller theory [cf. [AbsTopIII], §I5], the portion of
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 169
the infinite chain of Θ×μ-links of Corollary 4.10, (vi), parametrized by n ≤ 0
Θ×μ
...
−→ (n−1)HT Θ±ellNF Θ×μ
−→ nHT Θ±ellNF Θ×μ
−→...
Θ×μ
−→ 0HT Θ±ellNF
may be thought of as corresponding to the canonical liftings of p-adic Teichm¨ uller
theory. That is to say, each Θ±ellNF-Hodge theater — which one may think of as
representing the conventional scheme theory surrounding the given number field
equipped with an elliptic curve — corresponds to a hyperbolic curve in posi-
tive characteristic equipped with a nilpotent ordinary indigenous bundle [cf. the
discussion of [AbsTopIII], §I5]. The theta functions that give rise to the Θ×μ-links
may be thought of as specifying the specific canonical deformation [cf. the discus-
sion of (i)] that gives rise to this “canonical lifting”. The canonical Frobenius
lifting on this canonical lifting may be thought of as corresponding to the theory
to be developed in [IUTchIII]. From this point of view, the passage
theta functions, number fields Gaussian distributions
[cf. the discussion of Remark 4.11.2] eﬀected in the theory of the present series
of papers presented thus far — i.e., at a more concrete level, the passage, via
Hodge-Arakelov-theoretic evaluation, from the above semi-infinite chain to
the corresponding semi-infinite chain
Θ×μ
...
gau −→ (n−1)HT Θ±ellNF Θ×μ
gau −→ nHT Θ±ellNF Θ×μ
Θ×μ
gau −→...
gau −→ 0HT Θ±ellNF
of Θ×μ
gau-links — may be thought of as corresponding to the passage
MF∇-objects Galois representations
in the case of the canonical indigenous bundles that occur in p-adic Teichm¨ uller
theory — cf. the discussion of [pTeich], Introduction, §1.3, §1.7; the discussion in
[HASurI], §1.3, §1.4, of the relationship between such canonical indigenous bundles
in the case of the moduli stack of elliptic curves and the scheme-theoretic Hodge-
Arakelov theory of [HASurI], [HASurII]. Put another way, it corresponds to the
passagefromthinkingofthe“canonicallifting”asacurveequippedwiththeMF∇
-
object constituted by a canonical Frobenius-invariant indigenous bundle to thinking
ofthe“canonicallifting”asacurveequippedwithacanonical Galois representation,
i.e., a canonical crystalline representation [that is to say, a representation that
happens to arise from an MF∇-object] of the arithmetic fundamental group of the
generic fiber of the curve into PGL2(Zp).
(iii) The analogy between the theory of the present series of papers and p-adic
Teichm¨ uller theory may also be seen, at a more technical level, in the following
correspondences between various aspects of the theory presented thus far in the
present series of papers and various aspects of the theory of [CanLift], §3 [cf. also
Remark 4.11.5 below]:
(a) The discussion of (ii) above is reminiscent of the important role played by
the canonical Galois representation in the absolute p-adic anabelian
theory of [CanLift], §3 [cf. the proof of [CanLift], Lemma 3.5].
170 SHINICHI MOCHIZUKI
(b) In light of the important role played, in the present series of papers,
by mono-theta-theoretic cyclotomic rigidity [which was reviewed in
Definition 1.1, (ii); Remark 1.1.1], it is perhaps of interest to recall [cf.
Remark 1.11.6] the important role played by cyclotomic rigidity isomor-
phisms in the theory of [CanLift], §3, via the theory of [AbsAnab], §2
[cf., especially, [AbsAnab], Lemmas 2.5, 2.6]. On the other hand, at the
level of direct correspondences between the theory of the present series
of papers and p-adic Teichm¨ uller theory, it is perhaps better to think
of mono-theta-theoretic cyclotomic rigidity as corresponding to the local
uniformizations arising from the canonical indigenous bundle [cf. the
discussion of Remark 3.6.5, (iii)].
(c) The important role played, in the present series of papers, by the “two-
dimensional symmetry” constituted by the F ±
l- and Fl -symmetries
— whose two-dimensionality may be thought of as corresponding to the
two real dimensions of the complex upper half-plane [cf. the discussion
of [IUTchI], Remark 6.12.3, (iii)] — is reminiscent of the important role
played in the theory of [CanLift], §3, in eﬀect, by the vanishing of the
zero-th group cohomology module
H0(Ad(−))
of the canonical Galois representation associated to the canonical indige-
nous bundle — cf. the various geometric conditions over the ordinary
locus and at the supersingular points of the mod p representations con-
sidered in [CanLift], Lemma 3.2. That is to say, the F ±
l -symmetry may
be regarded as corresponding to the unipotent monodromy over the
ordinary locus
1 ∗
0 1
∼
→ Fp
— which is isomorphic to the additive group underlying Fp — while
the Fl -symmetry may be regarded as corresponding to the toral mon-
odromy at the supersingular points
∗ 0
0 ∗−1
∼
→ F×
p
— which is isomorphic to the multiplicative group F×
p and arises from ex-
tracting a (p−1)-th root of the Hasse invariant. Moreover, the “intuitive,
conventional” nature of the theory over any single connected component
of the ordinary locus — a theory which allows one, for instance, to con-
struct q-parameters — is reminiscent of the uniradial nature of the F ±
l-
symmetry, while the fact that supersingular points lie simultaneously on
irreducible components obtained as closures of distinct connected com-
ponents of the ordinary locus is reminiscent of the multiradiality — i.e.,
compatibility with simultaneous execution in distinct Hodge theaters —
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 171
of the Fl -symmetry [cf. the discussion of Remark 4.7.4]. The above dis-
cussion is summarized, at the level of keywords, in Fig. 4.4 below.
F ±
l -symmetry Fl -symmetry
additive multiplicative
uniradial multiradial
monodromy over the ordinary locus monodromy at the
supersingular points
Fig. 4.4: Correspondence of symmetries with p-adic Teichm¨ uller theory
(d) The important role played, in the present series of papers, by conjugate
synchronization at the various evaluation points of the theta function
— which gives rise, in the form of the Gaussian distribution, to the
links between the various Θ±ellNF-Hodge theaters in the second semi-
infinite chain that appeared in the discussion of (ii) — is reminiscent of
the important role played in the theory of [CanLift], §3, by the description
given in [CanLift], Lemma 3.4, of the first group cohomology module
H1(Ad(−))
of the canonical Galois representation associated to the canonical indige-
nous bundle — whose “slope−1 portion” may be thought of as governing
the “links” between the “mod pn” and “mod pn+1” portions of the canon-
ical Galois representation, as it is considered in the proof of [CanLift],
Lemma 3.5. Here, we note that this description may be summarized, in
eﬀect, as asserting that the slope−1 portion in question is, up to tensor
product with an unramified Galois representation, isomorphic to a direct
product of 3g−3+r copies of Fp(−1) [where the “(−1)” denotes a Tate
twist] — a situation that is reminiscent of the l synchronized copies of
cyclotomesthatoccurinthecontextoftheevaluationofthethetafunction
considered in the present series of papers. Moreover, the deformations
of the canonical Galois representation parametrized by this module
“H1(Ad(−))” may be thought of as corresponding, in the theory of the
present series of papers, to the “independent Aut(Gv)-indeterminacies”
[i.e., for v ∈ Vnon] that occur at each label ∈ Fl when one consider multi-
radial representations of Gaussian monoids—cf. thetheoryof[IUTchIII],
§3; [IUTchIII], Remark 3.12.4, (iii).
[Here, we note that, in fact, the various “−1’s” in (d) should be replaced by “1’s”
— cf. Remark 4.11.5 below.] Finally, we observe, with regard to (d), that the
172 SHINICHI MOCHIZUKI
description in question that appears in [CanLift], Lemma 3.4, may be thought of as
a reflection of the ordinarity [i.e., as opposed to just admissibility] of the positive
characteristicnilpotentindigenous bundleunder consideration, hence is reminiscent
of the discussion of [AbsTopIII], Remark 5.10.3, (ii), of the correspondence between
ordinarity in p-adic Teichm¨ uller theory and the theory of the´ etale theta function
developed in [EtTh].
Remark 4.11.5. We take this opportunity to correct a few notational errors
in the statement of the condition (†M) of [CanLift], Lemma 3.4, which, however,
do not aﬀect the proof of this lemma in any substantive way. The subquotient
“G2(M)” (respectively, “G−1”) should have been denoted “G−2(M)” (respectively,
“G1”). The subquotient G−2(M) (respectively, G1) is isomorphic to the tensor
product of an unramified module with a Tate twist Fp(−2) (respectively, Fp(1)).
That is to say, there is a sign error in the Tate twists stated in (†M). Finally, in
order to obtain the desired dimensions over Fp, one must replace the cohomology
module
“M def
= H1(ΔXlog,Ad(VFp))”
by the submodule of this module consisting of elements whose restriction to each of
the cuspidal inertia groups of ΔXlog is upper triangular with respect to the filtration
determined by the nilpotent monodromy action on VFp [i.e., by the cuspidal inertia
group in question]. That is to say, an elementary computation shows that the
operation of restriction to this submodule has the eﬀect of lowering the dimension
of G−2(M) from 3g−3+2r to 3g−3+r, as desired.
¨
INTER-UNIVERSAL TEICHM
ULLER THEORY II 173
Bibliography
[Lehto] O. Lehto, Univalent Functions and Teichm¨ uller Spaces, Graduate Texts in
Mathematics 109, Springer-Verlag (1987).
[pOrd] S. Mochizuki, A Theory of Ordinary p-adic Curves, Publ. Res. Inst. Math. Sci.
32 (1996), pp. 957-1151.
[pTeich] S. Mochizuki, Foundations of p-adic Teichm¨ uller Theory, AMS/IP Studies
in Advanced Mathematics 11, American Mathematical Society/International
Press (1999).
[pGC] S. Mochizuki, The Local Pro-p Anabelian Geometry of Curves, Invent. Math.
138 (1999), pp. 319-423.
[HASurI] S. Mochizuki, A Survey of the Hodge-Arakelov Theory of Elliptic Curves I,
Arithmetic Fundamental Groups and Noncommutative Algebra, Proceedings of
Symposia in Pure Mathematics 70, American Mathematical Society (2002),
pp. 533-569.
[HASurII] S. Mochizuki, A Survey of the Hodge-Arakelov Theory of Elliptic Curves II,
Algebraic Geometry 2000, Azumino, Adv. Stud. Pure Math. 36, Math. Soc.
Japan (2002), pp. 81-114.
[AbsAnab] S. Mochizuki, The Absolute Anabelian Geometry of Hyperbolic Curves, Galois
Theory and Modular Forms, Kluwer Academic Publishers (2004), pp. 77-122.
[CanLift] S. Mochizuki, The Absolute Anabelian Geometry of Canonical Curves, Kazuya
Kato’s fiftieth birthday, Doc. Math. 2003, Extra Vol., pp. 609-640.
[AbsSect] S. Mochizuki, Galois Sections in Absolute Anabelian Geometry, Nagoya Math.
J. 179 (2005), pp. 17-45.
[SemiAnbd] S. Mochizuki, Semi-graphs of Anabelioids, Publ. Res. Inst. Math. Sci. 42
(2006), pp. 221-322.
[CombGC] S. Mochizuki, A combinatorial version of the Grothendieck conjecture, Tohoku
Math. J. 59 (2007), pp. 455-479.
[Cusp] S. Mochizuki, Absolute anabelian cuspidalizations of proper hyperbolic curves,
J. Math. Kyoto Univ. 47 (2007), pp. 451-539.
[FrdI] S. Mochizuki, The Geometry of Frobenioids I: The General Theory, Kyushu J.
Math. 62 (2008), pp. 293-400.
[FrdII] S. Mochizuki, The Geometry of Frobenioids II: Poly-Frobenioids, Kyushu J.
Math. 62 (2008), pp. 401-460.
´
[EtTh] S. Mochizuki, The
Etale Theta Function and its Frobenioid-theoretic Manifes-
tations, Publ. Res. Inst. Math. Sci. 45 (2009), pp. 227-349.
[AbsTopI] S. Mochizuki, Topics in Absolute Anabelian Geometry I: Generalities, J. Math.
Sci. Univ. Tokyo 19 (2012), pp. 139-242.
[AbsTopII] S.Mochizuki,TopicsinAbsoluteAnabelianGeometryII:DecompositionGroups
and Endomorphisms, J. Math. Sci. Univ. Tokyo 20 (2013), pp. 171-269.
174 SHINICHI MOCHIZUKI
[AbsTopIII] S. Mochizuki, Topics in Absolute Anabelian Geometry III: Global Reconstruc-
tion Algorithms, J. Math. Sci. Univ. Tokyo 22 (2015), pp. 939-1156.
[IUTchI] S. Mochizuki, Inter-universal Teichm¨ uller Theory I: Construction of Hodge
Theaters, RIMS Preprint 1756 (August 2012), to appear in Publ. Res. Inst.
Math. Sci.
[IUTchIII] S. Mochizuki, Inter-universal Teichm¨ uller Theory III: Canonical Splittings of
the Log-theta-lattice, RIMS Preprint 1758 (August 2012), to appear in Publ.
Res. Inst. Math. Sci.
[IUTchIV] S. Mochizuki, Inter-universal Teichm¨ uller Theory IV: Log-volume Computa-
tions and Set-theoretic Foundations, RIMS Preprint 1759 (August 2012), to
appear in Publ. Res. Inst. Math. Sci.
[NSW] J.Neukirch,A.Schmidt,K.Wingberg,Cohomology of number fields,Grundlehren
der Mathematischen Wissenschaften 323, Springer-Verlag (2000).
[Szp] L. Szpiro, Degr´ es, intersections, hauteurs in Ast´ erisque 127 (1985), pp. 11-28.
Updated versions of preprints are available at the following webpage:
http://www.kurims.kyoto-u.ac.jp/~motizuki/papers-english.html
