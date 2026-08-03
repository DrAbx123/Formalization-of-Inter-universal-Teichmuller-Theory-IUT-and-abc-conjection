Why abc is still a conjecture
PETER SCHOLZE AND JAKOB STIX
In March 2018, the authors spent a week in Kyoto at RIMS of intense and constructive
discussionswithProf.MochizukiandProf.Hoshiaboutthesuggestedproofoftheabc conjecture.
We thank our hosts for their hospitality and generosity which made this week very special.
We, the authors of this note, came to the conclusion that there is no proof. We are going to
explain where, in our opinion, the suggested proof has a problem, a problem so severe that in
our opinion small modifications will not rescue the proof strategy. We supplement our report
by mentioning dissenting views from Prof. Mochizuki and Prof. Hoshi about the issues we raise
with the proof and whether it constitutes a gap at all, cf. the report by Mochizuki.
1. With Belyi maps from IUTT to Vojta’s inequality and abc
1.1. The goal in terms of Vojta’s inequality. The abc-conjecture goes back to Masser and
Oesterlé in 1985:
Conjecture 1. Let ε>0. Then for all coprime integers a,b,c with a+ b+ c= 0 we have
log(max{|a|,|b|,|c|}) <(1 + ε)·
log(p) + O(1)
p|abc
where the constant O(1) depends only on ε.
The abc-conjecture is a special case for the projective line P1
Q with respect to the divisor
D= 0 + 1 + ∞of Vojta’s height inequality. The general Vojta inequality is conjectured for the
height function hωX(D)(P) of any hyperbolic curve (X,D), i.e. where ωX(D) is ample.
Definition 2. Let k be a number field, ok its ring of integers, and X/k a smooth projective
geometrically connected curve. We denote an algebraic closure of k by¯
k.
¯
(1) The absolute logarithmic root discriminant of a point P ∈X(
k) is
d(P) := d(κ(P)) := 1
[κ(P) : Q] log(|∆κ(P)/Q|)
where κ(P) is the residue field of the closed point of X supporting P, and ∆κ(P)/Q ∈Z
denotes the discriminant of κ(P)/Q.
(2) Let D ⊆X be a reduced (possibly empty) divisor and set X= X\D. For any closed
point P ∈X we define the logarithmic conductor n1
D(P) depending on the choice of
a proper regular ok-model X →Spec(ok) as follows.
Let D be the closure of D in X , and let κ(P) denote the residue field of P. For the
unique extension P : Spec(oκ(P)) →X of P we consider P−1(D) as an eﬀective divisor
on Spec(oκ(P)). We then set
n1
D(P) := deg(P−1(D)red) = 1
[κ(P) : Q] P(pv)∈D
log(N(v)).
Herepv istheprimeidealcorrespondingtothefiniteplacevofkofnormN(v) = #ok/pv.
Diﬀerent choices of models lead to logarithmic conductors that agree up to contributions
at a fixed finite set of places, hence up to O(1). Therefore n1
D(−) is well defined up to
Date: August 23, 2018.
1
2 PETER SCHOLZE AND JAKOB STIX
a bounded function. It counts, as an Arakelov degree, the number of places where P
becomes congruent to a point in the boundary divisor D.
Conjecture 3 (Uniform Vojta inequality for hyperbolic curves). Let k be a number field and
let X/k be a smooth geometrically connected curve with smooth compactification X such that
¯
ωX(D) is ample, where D = (X \X)red. Let ε > 0 and d ≥1. Then for all points P ∈X(
k)
with [κ(P) : Q] ≤d, we have
hωX(D)(P) <(1 + ε) d(P) + n1
D(P) + Oε,d,X(1) (1.1)
Remark 4. The uniform version of Vojta’s inequality with respect to the degree of the number
field as stated in Conjecture 3 behaves well under branched covers, cf. [GenEll, Proposition 1.7]
or [BG06, Theorem 14.416], and indeed is claimed to follow from Mochizuki’s proof.
For a thorough discussion of the abc conjecture in relation to Voijta’s conjecture we refer to
[BG06, §12–§14].
1.2. Frey curves. Using Belyi maps as in [Belyi, Theorem 2.5] we may reduce Conjecture 3 to
the moduli stack of elliptic curves Mell, i.e., to elliptic curves over number fields. In this case a
form of the inequality is conjectured as Szpiro’s conjecture.
More precisely, in [GenEll, Theorem 2.1 and §3, §4] Mochizuki describes a reduction for all
fixed d≥1 to an inequality for all number fields k of degree [k : Q] ≤d and all elliptic curves
E/k corresponding to points P ∈Mell(k), such that
(1) The local data at places above 2 and ∞belong to a compact set, hence continuous local
invariants at 2 and at ∞are bounded.
(2) The elliptic curve E/k has split semistable reduction everywhere1. Hence, using local
Tate uniformization
Grig
m →Grig
m /qZ
v ≃(E×k kv)rig
,
we have a collection of local Tate parameters qv ∈kv at finite places v of multiplicative
bad reduction, and a finite Arakelov divisor qE = E bad red. at vv(qv)·v of degree
deg(qE) = 1
[k: Q] v
v(qv) log(N(v)).
The corresponding height term h(P) with respect to log-diﬀerentials of Mell is then
thanks and subject to the constraints of (1) that allow us to ignore contributions at
infinite places:
h(P) = 1
6 deg(qE) + O(h(P)1/2 + 1). (1.2)
¯
Note that the degree of the boundary ∞=
Mell \Mell is 1/2 while the degree of the
sheaf of log-diﬀerentials is 1/12 explaining the factor of 6.
(3) There is a prime number ℓ= ℓ(P) such that
(i) there are constants c1,c2 >0 depending only on d with
h(P)1/2 ≤ℓ≤h(P)1/2
·(c1 + c2·log(h(P))), (1.3)
(ii) the image of the mod ℓ Galois representation contains SL2(Fℓ):
¯
ρ: Galk →GL(E[ℓ](
k)) ≃GL2(Fℓ),
(iii) locally at places v of bad reduction, the extension arising from the local Tate
parametrization
0 →µℓ →E[ℓ] →Z/ℓZ →0
does not split. The extension class is given by qv ∈k×
v /(k×
v )ℓ, so we require qv not
to be an ℓ-th power.
1Arbitrary elliptic curves E0/k0 are dealt with after scalar extension such that E= E0 ×k0 k acquires split
semistable reduction. This works because k can be chosen with a uniform bound on [k : k0], e.g., by adjoining
coordinates of all 12-torsion points.
Why abc is still a conjecture 3
The above set-up misses an exceptional list of elliptic curves (E/k without a “core”, with
complex multiplication, etc.) that is ‘sparse’ and can be dealt with separately. We omit the
details here.
Remark 5. For fixed d≥1 and any bound b>0 there are only finitely many E/kcorresponding
to P ∈Mell(k) as above with [k : Q] ≤d and h(P) ≤b. This follows from Faltings’ theorem
(Shafarevich conjecture) applied to the Weil restriction A= Rk|Q(E) which is an abelian variety
A/Q ofdimensionboundedbydandgoodreductionoutsideafixedfinitesetofprimesdepending
on the height bound b. There are only finitely many isomorphism classes of such abelian varieties
and the map E/k→A/Q has finite fibres.
Claim 6 ([IUTT-4, Theorem 1.10]). Fix a natural number d≥1.
There are functions αd,βd : N →R depending of d, such that αd(ℓ) →0, for ℓ →∞, and
βd(ℓ) = Od(1) and, for all number fields k of degree [k: Q] ≤d and elliptic curves E/k as above
corresponding to P ∈Mell(k) and ℓ= ℓ(P),
1
6 deg(qE) ≤(1 + αd(ℓ)) d(P) + n1
∞(P) + βd(ℓ)·ℓ.
If c>0 is such that (1.2) says h(P) ≤1
6 deg(qE) + c·(h(P)1/2 + 1) for all E/k as above, then
the inequalities of Claim 6 and (1.3) yield
h(P)· 1−
c·(1 + h(P)−1/2) + βd(ℓ)(c1 + c2·log(h(P)))
h(P)1/2 ≤(1 + αd(ℓ))(d(P) + n1
∞(P)).
Now we choose ε>0. As soon as for large h(P) and thus large ℓ= ℓ(P) ≥h(P)1/2 we have
0 <1 + αd(ℓ) < 1−
we conclude Vojta’s inequality
c·(1 + h(P)−1/2) + βd(ℓ)(c1 + c2·log(h(P)))
h(P)1/2·(1 + ε),
h(P) ≤(1 + ε)(d(P) + n1
∞(P)) + Oε,d(1)
by adjusting the constant in Oε,d(1) to cover the finitely many cases of small h(P), cf. Remark 5.
1.3. How IUTT derives the inequality. For an odd prime number ℓ we set
ℓ−1
ℓ :=
2.
Moreover, for a local Tate parameter qv ∈kv at a finite place v of split multiplicative reduction
of E we choose a 2ℓ-th root2
q
∈¯
kv
v
of qv uniquely defined up to a root of unity. These roots define the Arakelov divisor
=
v(q
)·v=
v
1
2ℓqE.
E bad red. at v
Claim 6 is deduced in [IUTT-4, Theorem 1.10] from an inequality that reads
−|log(q)|≤−|log(Θ)| (1.4)
and which is the main claim of [IUTT-3, Corollary 3.12], see our comments in Section §2.2. Note
that the symbols in (1.4) are not just ‘minus the absolute values of the logarithm of something’,
but they rather have a distinct involved meaning defined in [IUTT-3, page 16, Corollary 3.12].
In fact, the left side of (1.4) is nothing but
−|log(q)|=−deg(qE) =−
1
2ℓdeg(qE).
2These roots play a role later, see Sections §2.1.6-§2.1.9.
qE
4 PETER SCHOLZE AND JAKOB STIX
The right side of (1.4) is in essential approximation (d(P)v is the v-part of the logarithmic root
discriminant)
=
=
−|log(Θ)|≈ 1
ℓ
ℓ
v
j=1
j·d(P)v−j2 1
2ℓ[k: Q]v(qv) log N(v) (1.5)
1
ℓ (ℓ + 1)
1
ℓ (ℓ + 1)(2ℓ + 1)
ℓ·
2 d(P)−
ℓ·
12ℓ deg(qE)
ℓ + 1
2 d(P)−
1
6 deg(qE).
Substituting this back into (1.4) yields after solving for 1
6 deg(qE) that
1
6 deg(qE) 1−
12
ℓ(ℓ+ 1)
−1
·d(P).
The error in the is taken care of with a linear term in ℓ on the right side, so this achieves a
proof of Claim 6. We are going to argue that the reasoning for (1.5) in [IUTT-3, Corollary 3.12]
rather describes the following inequality (with the factor j2 missing):
−|log(Θ)|≈ 1
ℓ
ℓ
v
j=1
1
j·d(P)v−
2ℓ[k: Q]v(qv) log N(v) (1.6)
ℓ + 1
1
=
2·d(P)−
2ℓdeg(qE).
Starting from the corrected inequality we obtain
0 d(P)
which is essentially free of content.
2. Hodge theaters and Frobenioid prime strips
2.1. Glossary: IUTT-terminology and how we may think of these objects. The IUTT
papers introduce a large amount of terminology. To facilitate the discussion, we will describe
(only) the notions that are strictly relevant to explain what we regard as the error. This will
involve certain radical simplifications, and it might be argued that such simplifications strip
away all the interesting mathematics that forms the core of Mochizuki’s proof. Towards this
objection we can oﬀer four excuses:
(1) During our discussion in Kyoto, Mochizuki agreed that some of these simplifications are
OK, for example regarding the critical notion of F ×µ-prime strips below.
(2) Generally, the discussions in Kyoto were at a level only slightly more sophisticated than
what is reflected in the simplifications below, and Mochizuki agreed that this does not
result in an essential obfuscation of the ideas. We also discussed the deeper parts of
the theory, and Mochizuki agreed that we had a good understanding of the substantial
mathematical content.
(3) When it comes to the more drastic simplifications indicated below, such as merely iden-
tifying the choice of a Hodge theater with the choice of a curve abstractly isomorphic to
X, or simply identifying identical objects along the identity, these are inessential to the
point we are making, and Mochizuki was not able to convince us during the week why
such a simplification was not allowed.
(4) We are certain that even with all subtleties restored, the issue we are pointing out
will prevail, and it is easier to point to the key issue with these surrounding subtleties
removed.
Why abc is still a conjecture 5
2.1.1. Initial Θ-data. This is essentially an elliptic curve E over a number field k, together
with a choice of a prime number ℓ, as above. Often, one considers instead the once-punctured
hyperbolic curve X= E\{0}.
There are many coverings of X that are considered in the IUTT papers, both over k and its
localizations. These will play no role for the following discussion, so we omit them here.
2.1.2. Hodge theater. These contain data of two types, “étale-like objects” and “Frobenius-like
objects”.
Roughly, the “étale-like data”, often denoted Dor D, is given by the abstract topological group
π1(X), considered as a group up to inner automorphism. Equivalently, as is done in the IUTT
papers, we may think of the abstract Galois category of finite étale covers of X, without a choice
of base point. At this point, it is useful to recall the following striking result of Mochizuki.
Theorem 7 ([Anab3, Theorem 1.9, Corollary 1.10]). Consider the category whose objects are
connected curves X of strictly Belyi type over a field k that is either a number field or a p-
adic field, and whose morphisms are finite étale morphisms of schemes. The functor taking
X to π1(X) defines a functor to the category whose objects are topological groups, and whose
morphisms G →H are H-conjugacy classes of injective open maps of topological groups. This
functor is fully faithful, and one can give an explicit quasi-inverse functor.
Moreover, once-punctured elliptic curves as considered in the IUTT papers, and their con-
nected finite étale covers, are of strictly Belyi type.3
Remark 8. In fact, a slightly stronger statement is true: One can extend the result to cover the
morphisms arising from Xkv
→X if X lives over a number field k and kv is a nonarchimedean
localization of k.
Remark 9. Anabelian geometry is supposed to be the key to Mochizuki’s proof. However, here
we see that in the IUTT papers, we are (for the essential part) in a situation where anabelian
geometry holds true in the sense that geometry and group theory are equivalent. We could not
find the point where it is essential to work with fundamental groups – there are no additional
isomorphisms of fundamental groups that do not come from isomorphisms of schemes, precisely
because of Mochizuki’s theorem.4
The“Frobenius-likepicture” isanenhancementofthe“étale-likepicture”, essentiallyconsisting
of the topological group π1(X) together with an action on a monoid, e.g. the group¯
k×of units
in¯
k.
of a topological group acting on a topological monoid (and isomorphisms as morphisms) to
the category of topological groups Π (and isomorphisms as morphisms) is an equivalence of
¯
k× → lim
−→
U⊂π1(X)
hyperbolic curve of genus 0.
a critical way.
categories on the essential image of X →(π1(X)
¯
k×). This is a consequence of Kummer
theory: As U ranges over open subgroups of π1(X), there is an injection
H1(U,Z(1)),
and there are almost no compatible automorphisms of¯
k×and its associated
¯
Z(1) = Hom(Q/Z,
k×)
3The final statement follows from the finite étale correspondence E\{0} [2] ←−E\E[2] →P1 \{0,1,λ,∞},
recalling that strictly Belyi type means that there is such a finite étale correspondence from the curve to a
4Such isomorphisms exist for Galois groups of p-adic fields, but this did not seem to enter the discussion in
5There is one notable more interesting case related to the monoid of divisors on tempered coverings of X at
places of bad reduction, by means of which Mochizuki encodes the Θ-function.5 Here again, in many situations the forgetful functor from the category of pairs (Π M)
6 PETER SCHOLZE AND JAKOB STIX
that commute with this injection: The automorphisms of the latter are just Z×, and except
for ±1, these do not respect the subset¯
k× along the above inclusion6. Thus, in this case the
assertion is only true up to sign, but for example if kv is a nonarchimedean localization, it
becomes true if one replaces¯
k×by
o¯
:= o¯
∩¯
k×
kv
kv
v.
This modification is often made in the IUTT papers.
We note that the monoid o×
¯
kv
¯
kv
“non-rigidity of the unit group portion”.
always.
1.1 (i)]. The logarithm map defines a well-defined surjective7 map
log : o×
K →K
(Q/Z)(1)∼
= oµ
K ⊂o×
K, and thus defining o
×µ
K := o×
K/oµ
∼
log : o
×µ
−→K .
K
(π1(X) o×
does not have this rigidity property: In this case, the pair
) admits extra automorphisms given by the action of Z× on o×
¯
. This is the
kv
Thus, up to equivalence of categories, the “Frobenius-like picture” is often equivalent to a
category of certain hyperbolic curves, cf. e.g. [IUTT-1, Corollary 5.3, Corollary 6.12 (i)], but not
In any case, a (Θ±ellNF-)Hodge theater is a certain amount of data that abstractly comes
from the fixed once-punctured elliptic curve X. The natural functor from the category whose
only object is X and whose morphisms are the automorphisms of X (which has one object with
two automorphisms, the ‘identity’ and ‘negation’) to the category of Θ±ellNF-Hodge theaters is
an equivalence of categories, as follows by combining [IUTT-1, Corollary 6.12 (i), Proposition 6.6
(iii), Corollary 5.6 (ii), Proposition 4.8 (ii), Definition 6.13]. In other words, up to equivalence
of categories, choosing a Hodge theater is equivalent to choosing a once-punctured elliptic curve
abstractlyisomorphictoX,andthisequivalenceofcategoriesisconstructiveinthesensethatone
can give an explicit functor that takes a Hodge theater and produces a once-punctured elliptic
curve. Of course, the category of elliptic curves abstractly isomorphic to X (and isomorphisms
of curves) is equivalent to the category whose only object is X that we started with.
2.1.3. log-links. The log-link introduced in [IUTT-3] is based on the following construction for
an algebraic closure K of a nonarchimedean local field of characteristic 0, cf. [IUTT-3, Definition
that turns multiplication into addition. The kernel of the map is given by the roots of unity
K, the logarithm induces a bijection
Using this observation, Mochizuki defines an endofunctor log on the category of topological fields
isomorphic to algebraic closures of nonarchimedean local fields as follows. For any such field K,
the underlying topological space of the new topological field log(K) will be o
×µ
K . The addition
on log(K) is given by the multiplication on o
×µ
K , and the multiplication on log(K) is defined via
transport of structure along the bijection
log : log(K) = o
×µ
∼
−→K.
K
It follows that the endofunctor log is naturally equivalent to the identity, with the natural
equivalence to the identity given by log : log(K)∼
= K.
The links in IUTT are all of the following form. Given two Hodge theaters HT1 and HT2,
one extracts certain coarse data of the same categorical type on both sides, and then chooses
an isomorphism between them. In the case of the log-link, the data is essentially that of π1(X)
acting on kv (for v ranging over the finite places; there is some similar story at the archimedean
6In fact, any ε∈ˆ
Z× that respects¯
¯
k× must also respect k×
=
k× ∩lim
k×/(k×)n sitting via Kummer theory
←−n
inside lim
−→U⊂π1 (X) H1(U,Z(1)). But k× is the direct sum of a finite torsion group with a free abelian group of
countable rank, hence multiplication by ε must preserve Z insideˆ
Z. This shows that necessarily ε= ±1.
7Note that K is algebraically closed and thus the image of log is divisible rather than contained in the
maximal ideal.
Why abc is still a conjecture 7
the log-link consists of an isomorphism Π1
∼
= Π2 and an isomorphism
olog(K1)
∼
= oK2
of topological monoids that is equivariant for the Π1
∼
= Π2-actions.8
2.1.4. Global realified Frobenioids. Mochizuki introduces the diﬃcult notion of a Frobenioid in
his papers [Frd1], [Frd2]. However, the notion of a global realified Frobenioid is very elemen-
tary, cf. [IUTT-1, Example 3.5]. In this case, it simply amounts to a collection of ordered
1-dimensional R-vector spaces Rv parametrized by the places v of k, together with a subspace
D0 ⊂
Rv
v
of codimension 1 such that there is an ordered isomorphism Rv
∼
= R under which D0 is the
kernel of the map
Rv
∼
=
R →R
v
v
given by sending 1 to log(N(v)) at finite places, and 2π at infinite places.
In other words, one can define another ordered 1-dimensional R-vector space
R⊙:= (
Rv)/D0,
v
and then the natural maps Rv →R⊙are ordered isomorphisms for all v. These considerations
show that the category of global realified Frobenioids is equivalent to the category of ordered
1-dimensional R-vector spaces. Moreover, if one fixes isomorphisms Rv
∼
= R as above and defines
γv ∈Rv as the preimage of 1, then the image of γv/log(N(v)) under the map Rv →R⊙(resp.
the image of γv/2π for infinite places v) is an element
γcan ∈R⊙
independentofv(butdependingonthetrivialization; cf.howeverthediscussionofF ×µ-prime
strips, where this trivialization is canonical).
2.1.5. F ×µ-prime strips. Another kind of coarse data that can be extracted from Hodge
theaters is the data of a F ×µ-prime strip, cf. [IUTT-2, Definition 4.9]. In general, prime
strips denote data that is parametrized by all places of the number field k. In the case of a
F ×µ-prime strip, this data is, at nonarchimedean places, given by the pair
×µ
¯
×o¯
kv
kv
where o¯
kv
≃N with trivial Gv = Galkv
-action.9 There is additional global data in the form of
a global realified Frobenioid. At each finite place, one defines Rv as the 1-dimensional R-vector
space with basis element γv given by the generator of o¯
kV , and one defines D0 ⊂ vRv as the
places that we will ignore). Letting Πi Ki denoting these pairs deduced from HTi for i= 1,2,
usual divisors of arithmetic degree 0. In other words, the forgetful functor from F ×µ-prime
strips to global realified Frobenioids factors over the category of trivialized global realified Frobe-
nioids, and the category of F ×µ-prime strips is equivalent to the product of the categories of
8Technically, Mochizuki does not choose any such isomorphism, but works with what he calls the full
poly-isomorphism, i.e. the set of all such isomorphisms. Although we spent a lot of time discussing the ne-
cessity of introducing full poly-isomorphisms over choosing one such isomorphism, Mochizuki was not able to
explain this convincingly in our opinion. On a related note, if one remembers that all Hodge theaters really come
from our fixed curve X, there is a completely natural isomorphism Π1
¯
K1
∼
= K2 as K1 =
k= K2, and thus a natural Π1
∼
= Π2-equivariant isomorphism log(K1)∼
the same on o ). Choosing these “obvious” isomorphisms did not result in any problem that would be solved by
allowing some other (possibly indeterminate) isomorphism.
9There is some extra structure called a ×µ-Kummer structure on o×µ
for all open subgroups H of Gv. As this plays no role for us, we will ignore it.Gv o
∼
= Π2 given by Π1 = π1(X) = Π2 and
= K1
∼
= K2 (and thus
¯
kv
, given as the images of (o×
¯
kv
)H →o×µ
¯
kv
8 PETER SCHOLZE AND JAKOB STIX
×µ
¯
×N,
kv
over all places v (where one has to modify this at archimedean places).
2.1.6. Abstract pilot objects. Pilot objects occur in [IUTT-3, Definition 3.8]. They essentially
consistofgeneratorsoftheo¯
-portionsofaF ×µ-primestrip. Onecandefinea“pilotelement”
kv
γpilot ∈R⊙
as the image of (v(q
)γv)v ∈ vRv (where we declare this entry to be 0 outside the places
v
of bad reduction) under the projection to R⊙= ( vRv)/D0 associated to the global realified
Frobenioid of the F ×µ-prime strip. Recall R⊙ is actually canonically trivialized by the
normalization that maps γcan to 1. Under this normalization, the pilot element becomes
1
R⊙∋γpilot →
2ldeg(qE) ∈R.
In many definitions below, the interesting things happen at the bad places, and we will only
discuss this part in detail.
2.1.7. Concrete q-pilot object. On the other hand, Mochizuki defines certain concrete10 pilot
objects: A q-pilot object and a Θ-pilot object. These are only defined internally within a Hodge
theater. The concrete q-pilot object is the collection of q
∈o¯
v
kv
at bad places (and certain
placeholder elements at other places). This is encoded in the F ×µ-prime strip F ×µ
by the collection of
×µ
¯
×qN
kv
v.
Note that the q
, when regarded as actual elements of o¯
kv, naturally define an Arakelov divisor,
whose Arakelov degree agrees with the number given by the abstract γpilot of F ×µ
chooses the natural isomorphism R⊙,q
∼
= R.
2.1.8. Concrete Θ-pilot object. The concrete Θ-pilot object is the collection of
qj2
∈o¯
v
kv
for j = 1,...,ℓ (at bad places). Up to some 2ℓ-th roots of unity, these arise naturally as the
values of a Θ-function at certain 2ℓ-torsion points, and Mochizuki devises an ingenious algorithm
to recover this data very directly from the data of π1(X) acting on a certain monoid of divisors
on tempered coverings of X.
The (j-th) concrete Θ-pilot object defines a natural Arakelov divisor whose Arakelov degree
equals j2 times the Arakelov degree of the q-pilot object.
On the other hand, one can form a F ×µ-prime strip F ×µ
Θ given by the pair
×µ
¯
kv
×((qj2
)j=1,...,ℓ )N
v
v
to the standard F ×µ-prime strip. In particular, the associated abstract pilot object (still
called the Θ-pilot object by Mochizuki) is an element of R⊙,Θ that encodes the arithmetic
degree of the j-th concrete Θ-pilot object only when the identification R⊙,Θ
j2; the necessity of this scaling is critical and will play a key role below.
Gv o
q given
v
q when one
11
that is generated by o
×µ
¯
kv
and (a formal symbol) (qj2
)j=1,...,ℓ ; these are all abstractly isomorphic
∼
= R is scaled by
pairs of topological groups acting on topological monoids abstractly isomorphic to Gv o
10The emphasis on abstract vs. concrete pilot objects is ours; Mochizuki does not properly distinguish them,
which is part of our main concern.
11There is an issue here that this is not one object but ℓ many. This can be resolved in a number of ways,
e.g. by passing to a “diagonal” copy; or more concretely by forming averages when one extracts numbers such as
arithmetic degrees.Gv o
Why abc is still a conjecture 9
2.1.9. Θ-link. The Θ-link between two Hodge theaters HT1 and HT2 is the (full poly-)isomorph-
ism between the F ×µ-prime strip F ×µ
Θ,1 constructed from the Θ-pilot object in HT1 and
the F ×µ-prime strip F ×µ
q,2 constructed from the q-pilot object in HT2. In particular, the
choice of such an isomorphism identifies the corresponding abstract pilot objects. However, the
Θ-link forgets about the concrete embeddings of q
into o¯
kv
and Θv ∼(qj2
)j=1,...,ℓ into o¯
kv
.
v
v
The attentive reader will realize that there is in fact a canonical choice for the Θ-link: The
×µ
¯
kv
the monoid N that appears that is called Θ respectively q.
the statement of Corollary 3.12, then one concludes [...] that −|log(q)|≤−|log(Θ)|∈R.”
the inequality follows directly.
necessary to change the isomorphism R∼
= R⊙,Θ by the scalar j2
spaces appearing:
(1) The ones R⊙,Θ, R⊙,q where the pilot elements γpilot of the abstract pilot objects live.
pilot objects live (of which there really are ℓ many in the case of Θ).
copies of them RΘ and Rq, one for each Hodge theater.
F ×µ-prime strips are given by data of the form Gv o
×N on both sides (at finite places),
and this data is canonically the same on both sides. It is simply the name of the generator of
2.2. Proof of [IUTT-3, Corollary 3.12]. Now let us try to unravel what happens in the critical
step in the series of papers, namely towards the end of Step (xi) in the proof of [IUTT-3,
Corollary 3.12]: “If one interprets the above discussion in terms of the notation introduced in
An extremely rough outline of what happens in this step is the following. One considers two
Hodge theaters HT1 and HT2 linked by a Θ-link, so in particular the abstract Θ-pilot object
from HT1 is mapped to the abstract q-pilot object belonging to HT2. As we indicated earlier,
there is no clear distinction between abstract and concrete pilot objects in Mochizuki’s work,
so it is argued in [IUTT-3, Corollary 3.12] that the multiradial algorithm [IUTT-3, Theorem
3.11]12 implies that up to certain indeterminacies, e.g. (Ind 1,2,3) (without which the conclusion
would be obviously false), this becomes an identification of concrete Θ-pilot objects and concrete
q-pilot objects (encoded via their action on processions of tensor packets of log-shells), and then
As we are interested in comparing real numbers, and we have seen that various copies of
ordered 1-dimensional R-vector spaces arise, it is critical to spell out all identifications of copies
of real numbers that are in place. In particular, in order to say that the abstract Θ-pilot
object encodes the arithmetic degree of the (j-th) concrete Θ-pilot object, we saw that it was
, j = 1,...,ℓ (or their average,
if one is interested in the averaged degree). Trying to unravel exactly what is going on, we
were drawing the following diagram in Kyoto. There are several ordered 1-dimensional R-vector
(2) The ones R⊙c,Θj, j = 1,...,ℓ , and R⊙c,q where the pilot elements γpilot of the concrete
(3) The standard real numbers R where arithmetic degrees live. For clarity, we take two
In order for a meaningful inequality to be concluded, one must consistently identify all of
these. For this purpose, we were drawing the following diagram (the left half arises from HT1,
12We pause to observe that with the simplifications outlined above, such as identifying identical copies of
objects along the identity, the critical [IUTT-3, Theorem 3.11] does not become false, but trivial.
10 PETER SCHOLZE AND JAKOB STIX
the Θ-side, and the right half arises from HT2, the q-side):
R⊙,Θ
Θ-link
= //
∼
R⊙,q
xx
""
(R⊙c,Θj)j=1,...,ℓ
R⊙c,q
||
&&
=
RΘ
// Rq
There is one consistent choice of isomorphisms given by using the natural isomorphisms R⊙,Θ
∼
=
R⊙,q
∼
= R comingfromtheobservationthattheglobalrealifiedFrobenioidscomingfromF ×µ-
prime strips are always canonically trivial using the various γcan. However, we saw that with
these isomorphisms, the abstract Θ-pilot object does not encode the arithmetic degree of the
Θ-divisor. Thus, Mochizuki wanted to introduce scalars of j2 somewhere on the left part of this
diagram (which strictly speaking leads to inconsistencies, i.e. monodromy, on the left part of the
diagram alone, which arguably can be overcome by using averages). However, it is clear that
this will result in the whole diagram having monodromy j2, i.e., being inconsistent.
The conclusion of this discussion is that with consistent identifications of copies of real num-
bers, one must in (1.5) omit the scalars j2 that appear, which leads to an empty inequality.
We voiced these concerns in this form at the end of the fourth day of discussions. On the
fifth and final day, Mochizuki tried to explain to us why this is not a problem after all. In
particular, he claimed that up to the “blurring” given by certain indeterminacies the diagram
does commute; it seems to us that this statement means that the blurring must be by a factor
of at least O(ℓ2) rendering the inequality thus obtained useless.
References
[BG06] Bombieri, E., Gubler, W., Heights in Diophantine geometry, volume 4 of New Mathematical Mono-
graphs, Cambridge University Press, Cambridge, 2006.
[GenEll] Mochizuki, S., Arithmetic elliptic curves in general position, Math. J. Okayama Univ., 52 (2010),
1–28.
[Belyi] Mochizuki, S., Non-critical Belyi maps, Math. J. Okayama Univ., 46 (2004), 105–113.
[Frd1] Mochizuki, S., The Geometry of Frobenioids I: The General Theory.
[Frd2] Mochizuki, S., The Geometry of Frobenioids II: Poly-Frobenioids.
[Anab3] Mochizuki, S., Topics in Absolute Anabelian Geometry III: Global Reconstruction Algorithms.
[IUTT-1] Mochizuki, S., Inter-universal Teichmuller Theory I: Construction of Hodge Theaters.
[IUTT-2] Mochizuki, S., Inter-universal Teichmuller Theory II: Hodge-Arakelov-theoretic Evaluation.
[IUTT-3] Mochizuki, S., Inter-universal Teichmuller Theory III: Canonical Splittings of the Log-theta-lattice.
[IUTT-4] Mochizuki, S., Inter-universal Teichmuller Theory IV: Log-volume Computations and Set-theoretic
Foundations.
Peter Scholze, Mathematisches Institut, Universität Bonn, Endenicher Allee 60, 53115 Bonn,
Germany
E-mail address: scholze@math.uni-bonn.de
Jakob Stix, Institut für Mathematik, Goethe–Universität Frankfurt, Robert-Mayer-Str. 6–8,
60325 Frankfurt am Main, Germany
E-mail address: stix@math.uni-frankfurt.de
