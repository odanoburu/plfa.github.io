---
src       : src/plfa/Relations.lagda
title     : "Relations: Inductive definition of relations"
layout    : page
prev      : /Induction/
permalink : /Relations/
next      : /Equality/
---

<pre class="Agda">{% raw %}<a id="170" class="Keyword">module</a> <a id="177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="192" class="Keyword">where</a>{% endraw %}</pre>

After having defined operations such as addition and multiplication,
the next step is to define relations, such as _less than or equal_.

## Imports

<pre class="Agda">{% raw %}<a id="373" class="Keyword">import</a> <a id="380" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="418" class="Symbol">as</a> <a id="421" class="Module">Eq</a>
<a id="424" class="Keyword">open</a> <a id="429" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="432" class="Keyword">using</a> <a id="438" class="Symbol">(</a><a id="439" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="442" class="Symbol">;</a> <a id="444" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="448" class="Symbol">;</a> <a id="450" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a><a id="454" class="Symbol">)</a>
<a id="456" class="Keyword">open</a> <a id="461" class="Keyword">import</a> <a id="468" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="477" class="Keyword">using</a> <a id="483" class="Symbol">(</a><a id="484" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="485" class="Symbol">;</a> <a id="487" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="491" class="Symbol">;</a> <a id="493" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="496" class="Symbol">;</a> <a id="498" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="501" class="Symbol">)</a>
<a id="503" class="Keyword">open</a> <a id="508" class="Keyword">import</a> <a id="515" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="535" class="Keyword">using</a> <a id="541" class="Symbol">(</a><a id="542" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#9708" class="Function">+-comm</a><a id="548" class="Symbol">)</a>{% endraw %}</pre>


## Defining relations

The relation _less than or equal_ has an infinite number of
instances.  Here are a few of them:

    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
<pre class="Agda">{% raw %}<a id="1225" class="Keyword">data</a> <a id="_≤_"></a><a id="1230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">_≤_</a> <a id="1234" class="Symbol">:</a> <a id="1236" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1238" class="Symbol">→</a> <a id="1240" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1242" class="Symbol">→</a> <a id="1244" class="PrimitiveType">Set</a> <a id="1248" class="Keyword">where</a>

  <a id="_≤_.z≤n"></a><a id="1257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a> <a id="1261" class="Symbol">:</a> <a id="1263" class="Symbol">∀</a> <a id="1265" class="Symbol">{</a><a id="1266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1266" class="Bound">n</a> <a id="1268" class="Symbol">:</a> <a id="1270" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1271" class="Symbol">}</a>
      <a id="1279" class="Comment">--------</a>
    <a id="1292" class="Symbol">→</a> <a id="1294" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="1299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="1301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1266" class="Bound">n</a>

  <a id="_≤_.s≤s"></a><a id="1306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="1310" class="Symbol">:</a> <a id="1312" class="Symbol">∀</a> <a id="1314" class="Symbol">{</a><a id="1315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1315" class="Bound">m</a> <a id="1317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1317" class="Bound">n</a> <a id="1319" class="Symbol">:</a> <a id="1321" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1322" class="Symbol">}</a>
    <a id="1328" class="Symbol">→</a> <a id="1330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1315" class="Bound">m</a> <a id="1332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="1334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1317" class="Bound">n</a>
      <a id="1342" class="Comment">-------------</a>
    <a id="1360" class="Symbol">→</a> <a id="1362" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1315" class="Bound">m</a> <a id="1368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="1370" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1317" class="Bound">n</a>{% endraw %}</pre>
Here `z≤n` and `s≤s` (with no spaces) are constructor names, while
`zero ≤ n`, and `m ≤ n` and `suc m ≤ suc n` (with spaces) are types.
This is our first use of an _indexed_ datatype, where the type `m ≤ n`
is indexed by two naturals, `m` and `n`.  In Agda any line beginning
with two or more dashes is a comment, and here we have exploited that
convention to write our Agda code in a form that resembles the
corresponding inference rules, a trick we will use often from now on.

Both definitions above tell us the same two things:

* _Base case_: for all naturals `n`, the proposition `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

* _Base case_: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

For example, here in inference rule notation is the proof that
`2 ≤ 4`:

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof:
<pre class="Agda">{% raw %}<a id="2652" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#2652" class="Function">_</a> <a id="2654" class="Symbol">:</a> <a id="2656" class="Number">2</a> <a id="2658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="2660" class="Number">4</a>
<a id="2662" class="Symbol">_</a> <a id="2664" class="Symbol">=</a> <a id="2666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="2670" class="Symbol">(</a><a id="2671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="2675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a><a id="2678" class="Symbol">)</a>{% endraw %}</pre>




## Implicit arguments

This is our first use of implicit arguments.  In the definition of
inequality, the two lines defining the constructors use `∀`, very
similar to our use of `∀` in propositions such as:

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
_implicit_ and need not be written explicitly; instead, they are
_inferred_ by Agda's typechecker. Thus, we write `+-comm m n` for the
proof that `m + n ≡ n + m`, but `z≤n` for the proof that `zero ≤ n`,
leaving `n` implicit.  Similarly, if `m≤n` is evidence that `m ≤ n`,
we write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving both `m`
and `n` implicit.

If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit:
<pre class="Agda">{% raw %}<a id="3673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3673" class="Function">_</a> <a id="3675" class="Symbol">:</a> <a id="3677" class="Number">2</a> <a id="3679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="3681" class="Number">4</a>
<a id="3683" class="Symbol">_</a> <a id="3685" class="Symbol">=</a> <a id="3687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="3691" class="Symbol">{</a><a id="3692" class="Number">1</a><a id="3693" class="Symbol">}</a> <a id="3695" class="Symbol">{</a><a id="3696" class="Number">3</a><a id="3697" class="Symbol">}</a> <a id="3699" class="Symbol">(</a><a id="3700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="3704" class="Symbol">{</a><a id="3705" class="Number">0</a><a id="3706" class="Symbol">}</a> <a id="3708" class="Symbol">{</a><a id="3709" class="Number">2</a><a id="3710" class="Symbol">}</a> <a id="3712" class="Symbol">(</a><a id="3713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a> <a id="3717" class="Symbol">{</a><a id="3718" class="Number">2</a><a id="3719" class="Symbol">}))</a>{% endraw %}</pre>
One may also identify implicit arguments by name:
<pre class="Agda">{% raw %}<a id="3797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3797" class="Function">_</a> <a id="3799" class="Symbol">:</a> <a id="3801" class="Number">2</a> <a id="3803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="3805" class="Number">4</a>
<a id="3807" class="Symbol">_</a> <a id="3809" class="Symbol">=</a> <a id="3811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="3815" class="Symbol">{</a><a id="3816" class="Argument">m</a> <a id="3818" class="Symbol">=</a> <a id="3820" class="Number">1</a><a id="3821" class="Symbol">}</a> <a id="3823" class="Symbol">{</a><a id="3824" class="Argument">n</a> <a id="3826" class="Symbol">=</a> <a id="3828" class="Number">3</a><a id="3829" class="Symbol">}</a> <a id="3831" class="Symbol">(</a><a id="3832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="3836" class="Symbol">{</a><a id="3837" class="Argument">m</a> <a id="3839" class="Symbol">=</a> <a id="3841" class="Number">0</a><a id="3842" class="Symbol">}</a> <a id="3844" class="Symbol">{</a><a id="3845" class="Argument">n</a> <a id="3847" class="Symbol">=</a> <a id="3849" class="Number">2</a><a id="3850" class="Symbol">}</a> <a id="3852" class="Symbol">(</a><a id="3853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a> <a id="3857" class="Symbol">{</a><a id="3858" class="Argument">n</a> <a id="3860" class="Symbol">=</a> <a id="3862" class="Number">2</a><a id="3863" class="Symbol">}))</a>{% endraw %}</pre>
In the latter format, you may only supply some implicit arguments:
<pre class="Agda">{% raw %}<a id="3958" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3958" class="Function">_</a> <a id="3960" class="Symbol">:</a> <a id="3962" class="Number">2</a> <a id="3964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="3966" class="Number">4</a>
<a id="3968" class="Symbol">_</a> <a id="3970" class="Symbol">=</a> <a id="3972" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="3976" class="Symbol">{</a><a id="3977" class="Argument">n</a> <a id="3979" class="Symbol">=</a> <a id="3981" class="Number">3</a><a id="3982" class="Symbol">}</a> <a id="3984" class="Symbol">(</a><a id="3985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="3989" class="Symbol">{</a><a id="3990" class="Argument">n</a> <a id="3992" class="Symbol">=</a> <a id="3994" class="Number">2</a><a id="3995" class="Symbol">}</a> <a id="3997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a><a id="4000" class="Symbol">)</a>{% endraw %}</pre>
It is not permitted to swap implicit arguments, even when named.


## Precedence

We declare the precedence for comparison as follows:
<pre class="Agda">{% raw %}<a id="4161" class="Keyword">infix</a> <a id="4167" class="Number">4</a> <a id="4169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">_≤_</a>{% endraw %}</pre>
We set the precedence of `_≤_` at level 4, so it binds less tightly
that `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Decidability

Given two numbers, it is straightforward to compute whether or not the
first is less than or equal to the second.  We don't give the code for
doing so here, but will return to this point in
Chapter [Decidable]({{ site.baseurl }}{% link out/plfa/Decidable.md%}).


## Properties of ordering relations

Relations pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Reflexive_. For all `n`, the relation `n ≤ n` holds.
* _Transitive_. For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
* _Anti-symmetric_. For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
* _Total_. For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

* _Preorder_. Any relation that is reflexive and transitive.
* _Partial order_. Any preorder that is also anti-symmetric.
* _Total order_. Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it is a preorder, partial order, or total order.  A
careful author will often call out these properties---or their
lack---for instance by saying that a newly introduced relation is a
partial order but not a total order.


#### Exercise `orderings` {#orderings}

Give an example of a preorder that is not a partial order.

<pre class="Agda">{% raw %}<a id="6238" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

Give an example of a partial order that is not a total order.

<pre class="Agda">{% raw %}<a id="6349" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity:
<pre class="Agda">{% raw %}<a id="≤-refl"></a><a id="6665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6665" class="Function">≤-refl</a> <a id="6672" class="Symbol">:</a> <a id="6674" class="Symbol">∀</a> <a id="6676" class="Symbol">{</a><a id="6677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6677" class="Bound">n</a> <a id="6679" class="Symbol">:</a> <a id="6681" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="6682" class="Symbol">}</a>
    <a id="6688" class="Comment">-----</a>
  <a id="6696" class="Symbol">→</a> <a id="6698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6677" class="Bound">n</a> <a id="6700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="6702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6677" class="Bound">n</a>
<a id="6704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6665" class="Function">≤-refl</a> <a id="6711" class="Symbol">{</a><a id="6712" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="6716" class="Symbol">}</a>   <a id="6720" class="Symbol">=</a>  <a id="6723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="6727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6665" class="Function">≤-refl</a> <a id="6734" class="Symbol">{</a><a id="6735" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="6739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6739" class="Bound">n</a><a id="6740" class="Symbol">}</a>  <a id="6743" class="Symbol">=</a>  <a id="6746" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="6750" class="Symbol">(</a><a id="6751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6665" class="Function">≤-refl</a> <a id="6758" class="Symbol">{</a><a id="6759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6739" class="Bound">n</a><a id="6760" class="Symbol">})</a>{% endraw %}</pre>
The proof is a straightforward induction on the implicit argument `n`.
In the base case, `zero ≤ zero` holds by `z≤n`.  In the inductive
case, the inductive hypothesis `≤-refl {n}` gives us a proof of `n ≤
n`, and applying `s≤s` to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`
hold, then `m ≤ p` holds.  Again, `m`, `n`, and `p` are implicit:
<pre class="Agda">{% raw %}<a id="≤-trans"></a><a id="7409" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7409" class="Function">≤-trans</a> <a id="7417" class="Symbol">:</a> <a id="7419" class="Symbol">∀</a> <a id="7421" class="Symbol">{</a><a id="7422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7422" class="Bound">m</a> <a id="7424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7424" class="Bound">n</a> <a id="7426" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7426" class="Bound">p</a> <a id="7428" class="Symbol">:</a> <a id="7430" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="7431" class="Symbol">}</a>
  <a id="7435" class="Symbol">→</a> <a id="7437" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7422" class="Bound">m</a> <a id="7439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="7441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7424" class="Bound">n</a>
  <a id="7445" class="Symbol">→</a> <a id="7447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7424" class="Bound">n</a> <a id="7449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="7451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7426" class="Bound">p</a>
    <a id="7457" class="Comment">-----</a>
  <a id="7465" class="Symbol">→</a> <a id="7467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7422" class="Bound">m</a> <a id="7469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="7471" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7426" class="Bound">p</a>
<a id="7473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7409" class="Function">≤-trans</a> <a id="7481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>       <a id="7491" class="Symbol">_</a>          <a id="7502" class="Symbol">=</a>  <a id="7505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="7509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7409" class="Function">≤-trans</a> <a id="7517" class="Symbol">(</a><a id="7518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="7522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7522" class="Bound">m≤n</a><a id="7525" class="Symbol">)</a> <a id="7527" class="Symbol">(</a><a id="7528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="7532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7532" class="Bound">n≤p</a><a id="7535" class="Symbol">)</a>  <a id="7538" class="Symbol">=</a>  <a id="7541" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="7545" class="Symbol">(</a><a id="7546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7409" class="Function">≤-trans</a> <a id="7554" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7522" class="Bound">m≤n</a> <a id="7558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7532" class="Bound">n≤p</a><a id="7561" class="Symbol">)</a>{% endraw %}</pre>
Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤
p`, which follows immediately by `z≤n`.  In this case, the fact that
`n ≤ p` is irrelevant, and we write `_` as the pattern to indicate
that the corresponding evidence is unused.

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that such a
case cannot arise, and does not require (or permit) it to be listed.

Alternatively, we could make the implicit parameters explicit:
<pre class="Agda">{% raw %}<a id="≤-trans′"></a><a id="8538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8538" class="Function">≤-trans′</a> <a id="8547" class="Symbol">:</a> <a id="8549" class="Symbol">∀</a> <a id="8551" class="Symbol">(</a><a id="8552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8552" class="Bound">m</a> <a id="8554" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8554" class="Bound">n</a> <a id="8556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8556" class="Bound">p</a> <a id="8558" class="Symbol">:</a> <a id="8560" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="8561" class="Symbol">)</a>
  <a id="8565" class="Symbol">→</a> <a id="8567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8552" class="Bound">m</a> <a id="8569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="8571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8554" class="Bound">n</a>
  <a id="8575" class="Symbol">→</a> <a id="8577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8554" class="Bound">n</a> <a id="8579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="8581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8556" class="Bound">p</a>
    <a id="8587" class="Comment">-----</a>
  <a id="8595" class="Symbol">→</a> <a id="8597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8552" class="Bound">m</a> <a id="8599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="8601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8556" class="Bound">p</a>
<a id="8603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8538" class="Function">≤-trans′</a> <a id="8612" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="8620" class="Symbol">_</a>       <a id="8628" class="Symbol">_</a>       <a id="8636" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>       <a id="8646" class="Symbol">_</a>          <a id="8657" class="Symbol">=</a>  <a id="8660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="8664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8538" class="Function">≤-trans′</a> <a id="8673" class="Symbol">(</a><a id="8674" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8678" class="Bound">m</a><a id="8679" class="Symbol">)</a> <a id="8681" class="Symbol">(</a><a id="8682" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8686" class="Bound">n</a><a id="8687" class="Symbol">)</a> <a id="8689" class="Symbol">(</a><a id="8690" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8694" class="Bound">p</a><a id="8695" class="Symbol">)</a> <a id="8697" class="Symbol">(</a><a id="8698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="8702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8702" class="Bound">m≤n</a><a id="8705" class="Symbol">)</a> <a id="8707" class="Symbol">(</a><a id="8708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="8712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8712" class="Bound">n≤p</a><a id="8715" class="Symbol">)</a>  <a id="8718" class="Symbol">=</a>  <a id="8721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="8725" class="Symbol">(</a><a id="8726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8538" class="Function">≤-trans′</a> <a id="8735" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8678" class="Bound">m</a> <a id="8737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8686" class="Bound">n</a> <a id="8739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8694" class="Bound">p</a> <a id="8741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8702" class="Bound">m≤n</a> <a id="8745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8712" class="Bound">n≤p</a><a id="8748" class="Symbol">)</a>{% endraw %}</pre>
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.

The technique of induction on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on 
values of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Anti-symmetry

The third property to prove about comparison is that it is
antisymmetric: for all naturals `m` and `n`, if both `m ≤ n` and `n ≤
m` hold, then `m ≡ n` holds:
<pre class="Agda">{% raw %}<a id="≤-antisym"></a><a id="9510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9510" class="Function">≤-antisym</a> <a id="9520" class="Symbol">:</a> <a id="9522" class="Symbol">∀</a> <a id="9524" class="Symbol">{</a><a id="9525" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9525" class="Bound">m</a> <a id="9527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9527" class="Bound">n</a> <a id="9529" class="Symbol">:</a> <a id="9531" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="9532" class="Symbol">}</a>
  <a id="9536" class="Symbol">→</a> <a id="9538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9525" class="Bound">m</a> <a id="9540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="9542" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9527" class="Bound">n</a>
  <a id="9546" class="Symbol">→</a> <a id="9548" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9527" class="Bound">n</a> <a id="9550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="9552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9525" class="Bound">m</a>
    <a id="9558" class="Comment">-----</a>
  <a id="9566" class="Symbol">→</a> <a id="9568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9525" class="Bound">m</a> <a id="9570" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="9572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9527" class="Bound">n</a>
<a id="9574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9510" class="Function">≤-antisym</a> <a id="9584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>       <a id="9594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>        <a id="9605" class="Symbol">=</a>  <a id="9608" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="9613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9510" class="Function">≤-antisym</a> <a id="9623" class="Symbol">(</a><a id="9624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="9628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9628" class="Bound">m≤n</a><a id="9631" class="Symbol">)</a> <a id="9633" class="Symbol">(</a><a id="9634" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="9638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9638" class="Bound">n≤m</a><a id="9641" class="Symbol">)</a>  <a id="9644" class="Symbol">=</a>  <a id="9647" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="9652" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9656" class="Symbol">(</a><a id="9657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9510" class="Function">≤-antisym</a> <a id="9667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9628" class="Bound">m≤n</a> <a id="9671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9638" class="Bound">n≤m</a><a id="9674" class="Symbol">)</a>{% endraw %}</pre>
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold.

In the base case, both inequalities hold by `z≤n`, and so we are given
`zero ≤ zero` and `zero ≤ zero` and must show `zero ≡ zero`, which
follows by reflexivity.  (Reflexivity of equality, that is, not
reflexivity of inequality.)

In the inductive case, the first inequality holds by `s≤s m≤n` and the
second inequality holds by `s≤s n≤m`, and so we are given `suc m ≤ suc n`
and `suc n ≤ suc m` and must show `suc m ≡ suc n`.  The inductive
hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`, and our goal
follows by congruence.

#### Exercise `≤-antisym-cases` {#leq-antisym-cases} 

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?

<pre class="Agda">{% raw %}<a id="10486" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total:
<pre class="Agda">{% raw %}<a id="10756" class="Keyword">data</a> <a id="Total"></a><a id="10761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10761" class="Datatype">Total</a> <a id="10767" class="Symbol">(</a><a id="10768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10768" class="Bound">m</a> <a id="10770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10770" class="Bound">n</a> <a id="10772" class="Symbol">:</a> <a id="10774" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10775" class="Symbol">)</a> <a id="10777" class="Symbol">:</a> <a id="10779" class="PrimitiveType">Set</a> <a id="10783" class="Keyword">where</a>

  <a id="Total.forward"></a><a id="10792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10792" class="InductiveConstructor">forward</a> <a id="10800" class="Symbol">:</a>
      <a id="10808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10768" class="Bound">m</a> <a id="10810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="10812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10770" class="Bound">n</a>
      <a id="10820" class="Comment">---------</a>
    <a id="10834" class="Symbol">→</a> <a id="10836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10761" class="Datatype">Total</a> <a id="10842" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10768" class="Bound">m</a> <a id="10844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10770" class="Bound">n</a>

  <a id="Total.flipped"></a><a id="10849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10849" class="InductiveConstructor">flipped</a> <a id="10857" class="Symbol">:</a>
      <a id="10865" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10770" class="Bound">n</a> <a id="10867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="10869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10768" class="Bound">m</a>
      <a id="10877" class="Comment">---------</a>
    <a id="10891" class="Symbol">→</a> <a id="10893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10761" class="Datatype">Total</a> <a id="10899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10768" class="Bound">m</a> <a id="10901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10770" class="Bound">n</a>{% endraw %}</pre>
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in Chapter [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md%}).)

This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype:
<pre class="Agda">{% raw %}<a id="11391" class="Keyword">data</a> <a id="Total′"></a><a id="11396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11396" class="Datatype">Total′</a> <a id="11403" class="Symbol">:</a> <a id="11405" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="11407" class="Symbol">→</a> <a id="11409" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="11411" class="Symbol">→</a> <a id="11413" class="PrimitiveType">Set</a> <a id="11417" class="Keyword">where</a>

  <a id="Total′.forward′"></a><a id="11426" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11426" class="InductiveConstructor">forward′</a> <a id="11435" class="Symbol">:</a> <a id="11437" class="Symbol">∀</a> <a id="11439" class="Symbol">{</a><a id="11440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11440" class="Bound">m</a> <a id="11442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11442" class="Bound">n</a> <a id="11444" class="Symbol">:</a> <a id="11446" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11447" class="Symbol">}</a>
    <a id="11453" class="Symbol">→</a> <a id="11455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11440" class="Bound">m</a> <a id="11457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="11459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11442" class="Bound">n</a>
      <a id="11467" class="Comment">----------</a>
    <a id="11482" class="Symbol">→</a> <a id="11484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11396" class="Datatype">Total′</a> <a id="11491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11440" class="Bound">m</a> <a id="11493" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11442" class="Bound">n</a>

  <a id="Total′.flipped′"></a><a id="11498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11498" class="InductiveConstructor">flipped′</a> <a id="11507" class="Symbol">:</a> <a id="11509" class="Symbol">∀</a> <a id="11511" class="Symbol">{</a><a id="11512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11512" class="Bound">m</a> <a id="11514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11514" class="Bound">n</a> <a id="11516" class="Symbol">:</a> <a id="11518" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11519" class="Symbol">}</a>
    <a id="11525" class="Symbol">→</a> <a id="11527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11514" class="Bound">n</a> <a id="11529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="11531" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11512" class="Bound">m</a>
      <a id="11539" class="Comment">----------</a>
    <a id="11554" class="Symbol">→</a> <a id="11556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11396" class="Datatype">Total′</a> <a id="11563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11512" class="Bound">m</a> <a id="11565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11514" class="Bound">n</a>{% endraw %}</pre>
Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality:
<pre class="Agda">{% raw %}<a id="≤-total"></a><a id="12100" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12100" class="Function">≤-total</a> <a id="12108" class="Symbol">:</a> <a id="12110" class="Symbol">∀</a> <a id="12112" class="Symbol">(</a><a id="12113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12113" class="Bound">m</a> <a id="12115" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12115" class="Bound">n</a> <a id="12117" class="Symbol">:</a> <a id="12119" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="12120" class="Symbol">)</a> <a id="12122" class="Symbol">→</a> <a id="12124" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10761" class="Datatype">Total</a> <a id="12130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12113" class="Bound">m</a> <a id="12132" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12115" class="Bound">n</a>
<a id="12134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12100" class="Function">≤-total</a> <a id="12142" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="12150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12150" class="Bound">n</a>                         <a id="12176" class="Symbol">=</a>  <a id="12179" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10792" class="InductiveConstructor">forward</a> <a id="12187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="12191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12100" class="Function">≤-total</a> <a id="12199" class="Symbol">(</a><a id="12200" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12204" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12204" class="Bound">m</a><a id="12205" class="Symbol">)</a> <a id="12207" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="12233" class="Symbol">=</a>  <a id="12236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10849" class="InductiveConstructor">flipped</a> <a id="12244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="12248" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12100" class="Function">≤-total</a> <a id="12256" class="Symbol">(</a><a id="12257" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12261" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12261" class="Bound">m</a><a id="12262" class="Symbol">)</a> <a id="12264" class="Symbol">(</a><a id="12265" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12269" class="Bound">n</a><a id="12270" class="Symbol">)</a> <a id="12272" class="Keyword">with</a> <a id="12277" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12100" class="Function">≤-total</a> <a id="12285" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12261" class="Bound">m</a> <a id="12287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12269" class="Bound">n</a>
<a id="12289" class="Symbol">...</a>                        <a id="12316" class="Symbol">|</a> <a id="12318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10792" class="InductiveConstructor">forward</a> <a id="12326" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12326" class="Bound">m≤n</a>  <a id="12331" class="Symbol">=</a>  <a id="12334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10792" class="InductiveConstructor">forward</a> <a id="12342" class="Symbol">(</a><a id="12343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="12347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12326" class="Bound">m≤n</a><a id="12350" class="Symbol">)</a>
<a id="12352" class="Symbol">...</a>                        <a id="12379" class="Symbol">|</a> <a id="12381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10849" class="InductiveConstructor">flipped</a> <a id="12389" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12389" class="Bound">n≤m</a>  <a id="12394" class="Symbol">=</a>  <a id="12397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10849" class="InductiveConstructor">flipped</a> <a id="12405" class="Symbol">(</a><a id="12406" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="12410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12389" class="Bound">n≤m</a><a id="12413" class="Symbol">)</a>{% endraw %}</pre>
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

* _First base case_: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

* _Second base case_: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

* _Inductive case_: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  + The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  + The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following:
<pre class="Agda">{% raw %}<a id="≤-total′"></a><a id="13921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13921" class="Function">≤-total′</a> <a id="13930" class="Symbol">:</a> <a id="13932" class="Symbol">∀</a> <a id="13934" class="Symbol">(</a><a id="13935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13935" class="Bound">m</a> <a id="13937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13937" class="Bound">n</a> <a id="13939" class="Symbol">:</a> <a id="13941" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="13942" class="Symbol">)</a> <a id="13944" class="Symbol">→</a> <a id="13946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10761" class="Datatype">Total</a> <a id="13952" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13935" class="Bound">m</a> <a id="13954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13937" class="Bound">n</a>
<a id="13956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13921" class="Function">≤-total′</a> <a id="13965" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="13973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13973" class="Bound">n</a>        <a id="13982" class="Symbol">=</a>  <a id="13985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10792" class="InductiveConstructor">forward</a> <a id="13993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="13997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13921" class="Function">≤-total′</a> <a id="14006" class="Symbol">(</a><a id="14007" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14011" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14011" class="Bound">m</a><a id="14012" class="Symbol">)</a> <a id="14014" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>     <a id="14023" class="Symbol">=</a>  <a id="14026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10849" class="InductiveConstructor">flipped</a> <a id="14034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="14038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13921" class="Function">≤-total′</a> <a id="14047" class="Symbol">(</a><a id="14048" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14052" class="Bound">m</a><a id="14053" class="Symbol">)</a> <a id="14055" class="Symbol">(</a><a id="14056" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14060" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14060" class="Bound">n</a><a id="14061" class="Symbol">)</a>  <a id="14064" class="Symbol">=</a>  <a id="14067" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14099" class="Function">helper</a> <a id="14074" class="Symbol">(</a><a id="14075" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13921" class="Function">≤-total′</a> <a id="14084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14052" class="Bound">m</a> <a id="14086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14060" class="Bound">n</a><a id="14087" class="Symbol">)</a>
  <a id="14091" class="Keyword">where</a>
  <a id="14099" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14099" class="Function">helper</a> <a id="14106" class="Symbol">:</a> <a id="14108" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10761" class="Datatype">Total</a> <a id="14114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14052" class="Bound">m</a> <a id="14116" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14060" class="Bound">n</a> <a id="14118" class="Symbol">→</a> <a id="14120" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10761" class="Datatype">Total</a> <a id="14126" class="Symbol">(</a><a id="14127" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14131" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14052" class="Bound">m</a><a id="14132" class="Symbol">)</a> <a id="14134" class="Symbol">(</a><a id="14135" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14060" class="Bound">n</a><a id="14140" class="Symbol">)</a>
  <a id="14144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14099" class="Function">helper</a> <a id="14151" class="Symbol">(</a><a id="14152" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10792" class="InductiveConstructor">forward</a> <a id="14160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14160" class="Bound">m≤n</a><a id="14163" class="Symbol">)</a>  <a id="14166" class="Symbol">=</a>  <a id="14169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10792" class="InductiveConstructor">forward</a> <a id="14177" class="Symbol">(</a><a id="14178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="14182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14160" class="Bound">m≤n</a><a id="14185" class="Symbol">)</a>
  <a id="14189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14099" class="Function">helper</a> <a id="14196" class="Symbol">(</a><a id="14197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10849" class="InductiveConstructor">flipped</a> <a id="14205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14205" class="Bound">n≤m</a><a id="14208" class="Symbol">)</a>  <a id="14211" class="Symbol">=</a>  <a id="14214" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10849" class="InductiveConstructor">flipped</a> <a id="14222" class="Symbol">(</a><a id="14223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="14227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14205" class="Bound">n≤m</a><a id="14230" class="Symbol">)</a>{% endraw %}</pre>
This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound on the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case:
<pre class="Agda">{% raw %}<a id="≤-total″"></a><a id="14868" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14868" class="Function">≤-total″</a> <a id="14877" class="Symbol">:</a> <a id="14879" class="Symbol">∀</a> <a id="14881" class="Symbol">(</a><a id="14882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14882" class="Bound">m</a> <a id="14884" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14884" class="Bound">n</a> <a id="14886" class="Symbol">:</a> <a id="14888" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="14889" class="Symbol">)</a> <a id="14891" class="Symbol">→</a> <a id="14893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10761" class="Datatype">Total</a> <a id="14899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14882" class="Bound">m</a> <a id="14901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14884" class="Bound">n</a>
<a id="14903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14868" class="Function">≤-total″</a> <a id="14912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14912" class="Bound">m</a>       <a id="14920" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="14946" class="Symbol">=</a>  <a id="14949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10849" class="InductiveConstructor">flipped</a> <a id="14957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="14961" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14868" class="Function">≤-total″</a> <a id="14970" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="14978" class="Symbol">(</a><a id="14979" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14983" class="Bound">n</a><a id="14984" class="Symbol">)</a>                   <a id="15004" class="Symbol">=</a>  <a id="15007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10792" class="InductiveConstructor">forward</a> <a id="15015" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="15019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14868" class="Function">≤-total″</a> <a id="15028" class="Symbol">(</a><a id="15029" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15033" class="Bound">m</a><a id="15034" class="Symbol">)</a> <a id="15036" class="Symbol">(</a><a id="15037" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15041" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15041" class="Bound">n</a><a id="15042" class="Symbol">)</a> <a id="15044" class="Keyword">with</a> <a id="15049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14868" class="Function">≤-total″</a> <a id="15058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15033" class="Bound">m</a> <a id="15060" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15041" class="Bound">n</a>
<a id="15062" class="Symbol">...</a>                        <a id="15089" class="Symbol">|</a> <a id="15091" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10792" class="InductiveConstructor">forward</a> <a id="15099" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15099" class="Bound">m≤n</a>   <a id="15105" class="Symbol">=</a>  <a id="15108" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10792" class="InductiveConstructor">forward</a> <a id="15116" class="Symbol">(</a><a id="15117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="15121" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15099" class="Bound">m≤n</a><a id="15124" class="Symbol">)</a>
<a id="15126" class="Symbol">...</a>                        <a id="15153" class="Symbol">|</a> <a id="15155" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10849" class="InductiveConstructor">flipped</a> <a id="15163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15163" class="Bound">n≤m</a>   <a id="15169" class="Symbol">=</a>  <a id="15172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10849" class="InductiveConstructor">flipped</a> <a id="15180" class="Symbol">(</a><a id="15181" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="15185" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15163" class="Bound">n≤m</a><a id="15188" class="Symbol">)</a>{% endraw %}</pre>
It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is _monotonic_ with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning:

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right:
<pre class="Agda">{% raw %}<a id="+-monoʳ-≤"></a><a id="15793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15793" class="Function">+-monoʳ-≤</a> <a id="15803" class="Symbol">:</a> <a id="15805" class="Symbol">∀</a> <a id="15807" class="Symbol">(</a><a id="15808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15808" class="Bound">m</a> <a id="15810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15810" class="Bound">p</a> <a id="15812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15812" class="Bound">q</a> <a id="15814" class="Symbol">:</a> <a id="15816" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="15817" class="Symbol">)</a>
  <a id="15821" class="Symbol">→</a> <a id="15823" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15810" class="Bound">p</a> <a id="15825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="15827" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15812" class="Bound">q</a>
    <a id="15833" class="Comment">-------------</a>
  <a id="15849" class="Symbol">→</a> <a id="15851" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15808" class="Bound">m</a> <a id="15853" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15810" class="Bound">p</a> <a id="15857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="15859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15808" class="Bound">m</a> <a id="15861" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15812" class="Bound">q</a>
<a id="15865" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15793" class="Function">+-monoʳ-≤</a> <a id="15875" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="15883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15883" class="Bound">p</a> <a id="15885" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15885" class="Bound">q</a> <a id="15887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15887" class="Bound">p≤q</a>  <a id="15892" class="Symbol">=</a>  <a id="15895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15887" class="Bound">p≤q</a>
<a id="15899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15793" class="Function">+-monoʳ-≤</a> <a id="15909" class="Symbol">(</a><a id="15910" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15914" class="Bound">m</a><a id="15915" class="Symbol">)</a> <a id="15917" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15917" class="Bound">p</a> <a id="15919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15919" class="Bound">q</a> <a id="15921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15921" class="Bound">p≤q</a>  <a id="15926" class="Symbol">=</a>  <a id="15929" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="15933" class="Symbol">(</a><a id="15934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15793" class="Function">+-monoʳ-≤</a> <a id="15944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15914" class="Bound">m</a> <a id="15946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15917" class="Bound">p</a> <a id="15948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15919" class="Bound">q</a> <a id="15950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15921" class="Bound">p≤q</a><a id="15953" class="Symbol">)</a>{% endraw %}</pre>
The proof is by induction on the first argument.

* _Base case_: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

* _Inductive case_: The first argument is `suc m`, in which case
  `suc m + p ≤ suc m + q` simplifies to `suc (m + p) ≤ suc (m + q)`.
  The inductive hypothesis `+-monoʳ-≤ m p q p≤q` establishes that
  `m + p ≤ m + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition:
<pre class="Agda">{% raw %}<a id="+-monoˡ-≤"></a><a id="16609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16609" class="Function">+-monoˡ-≤</a> <a id="16619" class="Symbol">:</a> <a id="16621" class="Symbol">∀</a> <a id="16623" class="Symbol">(</a><a id="16624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16624" class="Bound">m</a> <a id="16626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16626" class="Bound">n</a> <a id="16628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16628" class="Bound">p</a> <a id="16630" class="Symbol">:</a> <a id="16632" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16633" class="Symbol">)</a>
  <a id="16637" class="Symbol">→</a> <a id="16639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16624" class="Bound">m</a> <a id="16641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="16643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16626" class="Bound">n</a>
    <a id="16649" class="Comment">-------------</a>
  <a id="16665" class="Symbol">→</a> <a id="16667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16624" class="Bound">m</a> <a id="16669" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16628" class="Bound">p</a> <a id="16673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="16675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16626" class="Bound">n</a> <a id="16677" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16628" class="Bound">p</a>
<a id="16681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16609" class="Function">+-monoˡ-≤</a> <a id="16691" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16691" class="Bound">m</a> <a id="16693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16693" class="Bound">n</a> <a id="16695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16695" class="Bound">p</a> <a id="16697" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16697" class="Bound">m≤n</a>  <a id="16702" class="Keyword">rewrite</a> <a id="16710" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#9708" class="Function">+-comm</a> <a id="16717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16691" class="Bound">m</a> <a id="16719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16695" class="Bound">p</a> <a id="16721" class="Symbol">|</a> <a id="16723" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#9708" class="Function">+-comm</a> <a id="16730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16693" class="Bound">n</a> <a id="16732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16695" class="Bound">p</a>  <a id="16735" class="Symbol">=</a> <a id="16737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15793" class="Function">+-monoʳ-≤</a> <a id="16747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16695" class="Bound">p</a> <a id="16749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16691" class="Bound">m</a> <a id="16751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16693" class="Bound">n</a> <a id="16753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16697" class="Bound">m≤n</a>{% endraw %}</pre>
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results:
<pre class="Agda">{% raw %}<a id="+-mono-≤"></a><a id="16967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16967" class="Function">+-mono-≤</a> <a id="16976" class="Symbol">:</a> <a id="16978" class="Symbol">∀</a> <a id="16980" class="Symbol">(</a><a id="16981" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16981" class="Bound">m</a> <a id="16983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16983" class="Bound">n</a> <a id="16985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16985" class="Bound">p</a> <a id="16987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16987" class="Bound">q</a> <a id="16989" class="Symbol">:</a> <a id="16991" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16992" class="Symbol">)</a>
  <a id="16996" class="Symbol">→</a> <a id="16998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16981" class="Bound">m</a> <a id="17000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="17002" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16983" class="Bound">n</a>
  <a id="17006" class="Symbol">→</a> <a id="17008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16985" class="Bound">p</a> <a id="17010" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="17012" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16987" class="Bound">q</a>
    <a id="17018" class="Comment">-------------</a>
  <a id="17034" class="Symbol">→</a> <a id="17036" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16981" class="Bound">m</a> <a id="17038" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17040" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16985" class="Bound">p</a> <a id="17042" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="17044" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16983" class="Bound">n</a> <a id="17046" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17048" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16987" class="Bound">q</a>
<a id="17050" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16967" class="Function">+-mono-≤</a> <a id="17059" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17059" class="Bound">m</a> <a id="17061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17061" class="Bound">n</a> <a id="17063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17063" class="Bound">p</a> <a id="17065" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17065" class="Bound">q</a> <a id="17067" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17067" class="Bound">m≤n</a> <a id="17071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17071" class="Bound">p≤q</a>  <a id="17076" class="Symbol">=</a>  <a id="17079" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7409" class="Function">≤-trans</a> <a id="17087" class="Symbol">(</a><a id="17088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16609" class="Function">+-monoˡ-≤</a> <a id="17098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17059" class="Bound">m</a> <a id="17100" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17061" class="Bound">n</a> <a id="17102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17063" class="Bound">p</a> <a id="17104" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17067" class="Bound">m≤n</a><a id="17107" class="Symbol">)</a> <a id="17109" class="Symbol">(</a><a id="17110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15793" class="Function">+-monoʳ-≤</a> <a id="17120" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17061" class="Bound">n</a> <a id="17122" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17063" class="Bound">p</a> <a id="17124" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17065" class="Bound">q</a> <a id="17126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17071" class="Bound">p≤q</a><a id="17129" class="Symbol">)</a>{% endraw %}</pre>
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

<pre class="Agda">{% raw %}<a id="17454" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality:
<pre class="Agda">{% raw %}<a id="17603" class="Keyword">infix</a> <a id="17609" class="Number">4</a> <a id="17611" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17621" class="Datatype Operator">_&lt;_</a>

<a id="17616" class="Keyword">data</a> <a id="_&lt;_"></a><a id="17621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17621" class="Datatype Operator">_&lt;_</a> <a id="17625" class="Symbol">:</a> <a id="17627" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="17629" class="Symbol">→</a> <a id="17631" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="17633" class="Symbol">→</a> <a id="17635" class="PrimitiveType">Set</a> <a id="17639" class="Keyword">where</a>

  <a id="_&lt;_.z&lt;s"></a><a id="17648" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17648" class="InductiveConstructor">z&lt;s</a> <a id="17652" class="Symbol">:</a> <a id="17654" class="Symbol">∀</a> <a id="17656" class="Symbol">{</a><a id="17657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17657" class="Bound">n</a> <a id="17659" class="Symbol">:</a> <a id="17661" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17662" class="Symbol">}</a>
      <a id="17670" class="Comment">------------</a>
    <a id="17687" class="Symbol">→</a> <a id="17689" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="17694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17621" class="Datatype Operator">&lt;</a> <a id="17696" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17657" class="Bound">n</a>

  <a id="_&lt;_.s&lt;s"></a><a id="17705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17705" class="InductiveConstructor">s&lt;s</a> <a id="17709" class="Symbol">:</a> <a id="17711" class="Symbol">∀</a> <a id="17713" class="Symbol">{</a><a id="17714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17714" class="Bound">m</a> <a id="17716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17716" class="Bound">n</a> <a id="17718" class="Symbol">:</a> <a id="17720" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17721" class="Symbol">}</a>
    <a id="17727" class="Symbol">→</a> <a id="17729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17714" class="Bound">m</a> <a id="17731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17621" class="Datatype Operator">&lt;</a> <a id="17733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17716" class="Bound">n</a>
      <a id="17741" class="Comment">-------------</a>
    <a id="17759" class="Symbol">→</a> <a id="17761" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17714" class="Bound">m</a> <a id="17767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17621" class="Datatype Operator">&lt;</a> <a id="17769" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17716" class="Bound">n</a>{% endraw %}</pre>
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
_irreflexive_ in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
_trichotomy_: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly when `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred to
Chapter [Negation]({{ site.baseurl }}{% link out/plfa/Negation.md%}).

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by
exploiting the corresponding properties of inequality.

#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

<pre class="Agda">{% raw %}<a id="18943" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `trichotomy` {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`.

Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation]({{ site.baseurl }}{% link out/plfa/Negation.md%}).)

<pre class="Agda">{% raw %}<a id="19432" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

<pre class="Agda">{% raw %}<a id="19657" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

<pre class="Agda">{% raw %}<a id="19816" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `<-trans-revisited` {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.

<pre class="Agda">{% raw %}<a id="20092" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_:
<pre class="Agda">{% raw %}<a id="20347" class="Keyword">data</a> <a id="even"></a><a id="20352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20352" class="Datatype">even</a> <a id="20357" class="Symbol">:</a> <a id="20359" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="20361" class="Symbol">→</a> <a id="20363" class="PrimitiveType">Set</a>
<a id="20367" class="Keyword">data</a> <a id="odd"></a><a id="20372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20372" class="Datatype">odd</a>  <a id="20377" class="Symbol">:</a> <a id="20379" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="20381" class="Symbol">→</a> <a id="20383" class="PrimitiveType">Set</a>

<a id="20388" class="Keyword">data</a> <a id="20393" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20352" class="Datatype">even</a> <a id="20398" class="Keyword">where</a>

  <a id="even.zero"></a><a id="20407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20407" class="InductiveConstructor">zero</a> <a id="20412" class="Symbol">:</a>
      <a id="20420" class="Comment">---------</a>
      <a id="20436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20352" class="Datatype">even</a> <a id="20441" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>

  <a id="even.suc"></a><a id="20449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20449" class="InductiveConstructor">suc</a>  <a id="20454" class="Symbol">:</a> <a id="20456" class="Symbol">∀</a> <a id="20458" class="Symbol">{</a><a id="20459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20459" class="Bound">n</a> <a id="20461" class="Symbol">:</a> <a id="20463" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20464" class="Symbol">}</a>
    <a id="20470" class="Symbol">→</a> <a id="20472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20372" class="Datatype">odd</a> <a id="20476" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20459" class="Bound">n</a>
      <a id="20484" class="Comment">------------</a>
    <a id="20501" class="Symbol">→</a> <a id="20503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20352" class="Datatype">even</a> <a id="20508" class="Symbol">(</a><a id="20509" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="20513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20459" class="Bound">n</a><a id="20514" class="Symbol">)</a>

<a id="20517" class="Keyword">data</a> <a id="20522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20372" class="Datatype">odd</a> <a id="20526" class="Keyword">where</a>

  <a id="odd.suc"></a><a id="20535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20535" class="InductiveConstructor">suc</a>   <a id="20541" class="Symbol">:</a> <a id="20543" class="Symbol">∀</a> <a id="20545" class="Symbol">{</a><a id="20546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20546" class="Bound">n</a> <a id="20548" class="Symbol">:</a> <a id="20550" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20551" class="Symbol">}</a>
    <a id="20557" class="Symbol">→</a> <a id="20559" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20352" class="Datatype">even</a> <a id="20564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20546" class="Bound">n</a>
      <a id="20572" class="Comment">-----------</a>
    <a id="20588" class="Symbol">→</a> <a id="20590" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20372" class="Datatype">odd</a> <a id="20594" class="Symbol">(</a><a id="20595" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="20599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20546" class="Bound">n</a><a id="20600" class="Symbol">)</a>{% endraw %}</pre>
A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.

This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

This is also our first use of _overloaded_ constructors,
that is, using the same name for constructors of different types.
Here `suc` means one of three constructors:

    suc : ℕ → ℕ

    suc : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

    suc : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)

Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.

We show that the sum of two even numbers is even:
<pre class="Agda">{% raw %}<a id="e+e≡e"></a><a id="21776" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21776" class="Function">e+e≡e</a> <a id="21782" class="Symbol">:</a> <a id="21784" class="Symbol">∀</a> <a id="21786" class="Symbol">{</a><a id="21787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21787" class="Bound">m</a> <a id="21789" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21789" class="Bound">n</a> <a id="21791" class="Symbol">:</a> <a id="21793" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="21794" class="Symbol">}</a>
  <a id="21798" class="Symbol">→</a> <a id="21800" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20352" class="Datatype">even</a> <a id="21805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21787" class="Bound">m</a>
  <a id="21809" class="Symbol">→</a> <a id="21811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20352" class="Datatype">even</a> <a id="21816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21789" class="Bound">n</a>
    <a id="21822" class="Comment">------------</a>
  <a id="21837" class="Symbol">→</a> <a id="21839" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20352" class="Datatype">even</a> <a id="21844" class="Symbol">(</a><a id="21845" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21787" class="Bound">m</a> <a id="21847" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="21849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21789" class="Bound">n</a><a id="21850" class="Symbol">)</a>

<a id="o+e≡o"></a><a id="21853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21853" class="Function">o+e≡o</a> <a id="21859" class="Symbol">:</a> <a id="21861" class="Symbol">∀</a> <a id="21863" class="Symbol">{</a><a id="21864" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21864" class="Bound">m</a> <a id="21866" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21866" class="Bound">n</a> <a id="21868" class="Symbol">:</a> <a id="21870" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="21871" class="Symbol">}</a>
  <a id="21875" class="Symbol">→</a> <a id="21877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20372" class="Datatype">odd</a> <a id="21881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21864" class="Bound">m</a>
  <a id="21885" class="Symbol">→</a> <a id="21887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20352" class="Datatype">even</a> <a id="21892" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21866" class="Bound">n</a>
    <a id="21898" class="Comment">-----------</a>
  <a id="21912" class="Symbol">→</a> <a id="21914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20372" class="Datatype">odd</a> <a id="21918" class="Symbol">(</a><a id="21919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21864" class="Bound">m</a> <a id="21921" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="21923" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21866" class="Bound">n</a><a id="21924" class="Symbol">)</a>

<a id="21927" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21776" class="Function">e+e≡e</a> <a id="21933" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20407" class="InductiveConstructor">zero</a>     <a id="21942" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21942" class="Bound">en</a>  <a id="21946" class="Symbol">=</a>  <a id="21949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21942" class="Bound">en</a>
<a id="21952" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21776" class="Function">e+e≡e</a> <a id="21958" class="Symbol">(</a><a id="21959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20449" class="InductiveConstructor">suc</a> <a id="21963" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21963" class="Bound">om</a><a id="21965" class="Symbol">)</a> <a id="21967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21967" class="Bound">en</a>  <a id="21971" class="Symbol">=</a>  <a id="21974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20449" class="InductiveConstructor">suc</a> <a id="21978" class="Symbol">(</a><a id="21979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21853" class="Function">o+e≡o</a> <a id="21985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21963" class="Bound">om</a> <a id="21988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21967" class="Bound">en</a><a id="21990" class="Symbol">)</a>

<a id="21993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21853" class="Function">o+e≡o</a> <a id="21999" class="Symbol">(</a><a id="22000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20535" class="InductiveConstructor">suc</a> <a id="22004" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22004" class="Bound">em</a><a id="22006" class="Symbol">)</a> <a id="22008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22008" class="Bound">en</a>  <a id="22012" class="Symbol">=</a>  <a id="22015" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20535" class="InductiveConstructor">suc</a> <a id="22019" class="Symbol">(</a><a id="22020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21776" class="Function">e+e≡e</a> <a id="22026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22004" class="Bound">em</a> <a id="22029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22008" class="Bound">en</a><a id="22031" class="Symbol">)</a>{% endraw %}</pre>
Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

To show that the sum of two even numbers is even, consider the
evidence that the first number is even. If it is because it is zero,
then the sum is even because the second number is even.  If it is
because it is the successor of an odd number, then the result is even
because it is the successor of the sum of an odd and an even number,
which is odd.

To show that the sum of an odd and even number is odd, consider the
evidence that the first number is odd. If it is because it is the
successor of an even number, then the result is odd because it is the
successor of the sum of two even numbers, which is even.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

<pre class="Agda">{% raw %}<a id="23185" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that 
Exercise [Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings:

    Can x
    ------------
    Can (inc x)

Show that converting a natural to a bitstring always yields a
canonical bitstring:

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity:

    Can x
    ---------------
    to (from x) ≡ x

(Hint: For each of these, you may first need to prove related
properties of `One`.)

<pre class="Agda">{% raw %}<a id="24479" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
<pre class="Agda">{% raw %}<a id="24631" class="Keyword">import</a> <a id="24638" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="24647" class="Keyword">using</a> <a id="24653" class="Symbol">(</a><a id="24654" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#845" class="Datatype Operator">_≤_</a><a id="24657" class="Symbol">;</a> <a id="24659" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#868" class="InductiveConstructor">z≤n</a><a id="24662" class="Symbol">;</a> <a id="24664" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#910" class="InductiveConstructor">s≤s</a><a id="24667" class="Symbol">)</a>
<a id="24669" class="Keyword">import</a> <a id="24676" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="24696" class="Keyword">using</a> <a id="24702" class="Symbol">(</a><a id="24703" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2115" class="Function">≤-refl</a><a id="24709" class="Symbol">;</a> <a id="24711" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2308" class="Function">≤-trans</a><a id="24718" class="Symbol">;</a> <a id="24720" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2165" class="Function">≤-antisym</a><a id="24729" class="Symbol">;</a> <a id="24731" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2420" class="Function">≤-total</a><a id="24738" class="Symbol">;</a>
                                  <a id="24774" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#12667" class="Function">+-monoʳ-≤</a><a id="24783" class="Symbol">;</a> <a id="24785" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#12577" class="Function">+-monoˡ-≤</a><a id="24794" class="Symbol">;</a> <a id="24796" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#12421" class="Function">+-mono-≤</a><a id="24804" class="Symbol">)</a>{% endraw %}</pre>
In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
Chapter [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md%})),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here,
and more arguments are implicit.


## Unicode

This chapter uses the following unicode:

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.
