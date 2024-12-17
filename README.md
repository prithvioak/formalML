# formalML
Formalizing machine learning concepts in Lean!

## Motivation
More and more, Machine Learning is becoming an integral part of the technology stack. But with the increasing complexity of models, it is becoming harder to understand the inner workings of these models; they are often seen as black boxes. There is a growing need for [explainable AI](https://www.ibm.com/topics/explainable-ai#:~:text=Explainable%20artificial%20intelligence%20(XAI)%20is,created%20by%20machine%20learning%20algorithms.), involving the ability to understand and trust the algorithms/models that are being used. 
Research is being done to increase the transparency & safety of these models. For example, DeepMind's [Frontier Safety Framework](https://deepmind.google/discover/blog/introducing-the-frontier-safety-framework/) does work on evaluating the capabilities of AI systems and the threats they pose. But there is another potential way to help achieve reliability and transparency—through formal verification of Machine Learning concepts.

Efforts have been made in this direction; for example, [A Formal Proof of PAC Learnability for Decision Stumps](https://jtristan.github.io/papers/cpp21.pdf) formalizes the PAC learnability of decision stumps in Lean. And in other languages—[Formalization of a Stochastic Approximation Theorem](https://arxiv.org/abs/2202.05959) does formalization on ML concepts in Coq.

In general, Lean can help us in formalizing proofs for some of the most fundamental concepts in Machine Learning!


## Project Goals
This project aims to do exactly that: formalize some of the most fundamental concepts and ideas in Machine Learning.

This starts with defining some of the building blocks of Machine Learning, such as:
- Classifiers (Thresholds, Halfspaces, etc.)
- Hypothesis classes
- Loss functions (0-1 loss, squared loss, etc.)
- Accuracy
- Shattering and VC-dimension

Using these formalized concepts, we can prove some of their properties and begin to consider even more complex concepts, such as PAC learnability!

Each of these proofs has its own significance in the field of Machine Learning, and similar proofs at a larger scale could be crucial in verifying the correctness of Machine Learning models. As an example, the proof of convexity of the squared loss function could be used to verify the correctness of a gradient descent algorithm that uses the squared loss function as its loss function!

## Implementation

Based on the definitions I constructed, I wrote proofs on the following topics:
- convexity of the squared loss function
- Bounds on accuracy
- Ability of a hypothesis to induce a set of points
- shattering and VC-dimension for threshold and halfspace classifiers

Of all the written proofs, two remain incomplete, the first due to a specific property on Finite Sets that is certainly true yet hard to solve on Lean, and the second due to the high complexity of VC-dimension proofs for higher dimensions. I have also left in some stems of ideas that could develop into complex but complete proofs, such as establishing PAC learnability for certain hypothesis classes!

It is worth mentioning the restrictive nature of Lean, which makes each fundamental idea, step, and proof very explicit. I see this as a double-edged sword: while it makes the proof more robust and less prone to errors, it also makes writing these systems very complex. My original inspiration for this was the paper on PAC learnability for decision stumps, but a quick look at the [repository](https://github.com/jtristan/stump-learnable) makes clear how such a proof on even the simplest of hypothesis classes can require extremely intricate setup and proof on Lean.

## Looking Forward
The ideas expressed in this project are certainly a baby step in the direction of formalizing truly applicable Machine Learning concepts. With more such rigorous proofs in this direction (and more support on Lean for these concepts), it could definitely be possible to see Lean as a tool for verifying the correctness of Machine Learning models :)

<!-- ### A note on switching projects
Originally, I aimed to work on something completely different–formalizing deductive reasoning and fallacies in Lean. My aim was to be able to apply this formalization to a self-defined object system similar to the one set up by [`LeanReasoner`](https://arxiv.org/html/2403.13312v1):
- Create a basic formalization for deductive reasoning:
    - Soundness
    - Validity
    - Completeness
    - Fallaciousness
- Prove properties on the formalization
- Create a basic formalization for various fallacies
    - Strawman argument
    - Circular reasoning
    - Ad hominem
    - False cause
    - Slippery slope
    And so on...
- Prove that these are fallacies
- Prove some things that are not fallacies
- Prove that these are not sound/complete/valid
- Prove properties on them
    - Circular reasoning is equivalent to begging the question (or not)
    - One fallacy implies another fallacy (or not)
- Take some real-world examples and prove that they are fallacies and hence not sound/complete/valid
    - Defined object system similar to the one set up by `LeanReasoner` ([paper linked here](https://arxiv.org/html/2403.13312v1))
- Potential metaprogramming to create a Lean system to automatically prove fallacies -->


## Sources
[A Formal Proof of PAC Learnability for Decision Stumps](https://jtristan.github.io/papers/cpp21.pdf)

[CS1420: Machine Learning](https://cs1420.vercel.app/)

[IBM: Explainable AI](https://www.ibm.com/topics/explainable-ai#:~:text=Explainable%20artificial%20intelligence%20(XAI)%20is,created%20by%20machine%20learning%20algorithms.)


<!-- [Intro to Logic](http://intrologic.stanford.edu/videos/video_01.html?section=1)

[LeanReasoner: Boosting Complex Logical Reasoning with Lean](https://arxiv.org/html/2403.13312v1)

[Intuitionistic Propositional Logic](https://arxiv.org/pdf/2410.23765) -->