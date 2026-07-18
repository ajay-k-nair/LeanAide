# LeanAide: Extensible Autoformalization by Combinator Code Generation

Ajay Kumar Nair


## Abstract

Autoformalisation is the process of automatically translating natural language mathematics into machine-verifiable code. The most succesfull machine-verifiable format in this case are the theorem provers and among them Lean has found much success as an interactive theorem provers in recent times. 

LeanAide is an attempt at autoformalisation into Lean Theorem prover which offers modularity, extensibility in many aspects i.e., use of AI models of one's choice, adding combinators to suit specific domains. As strong autoformalisation agents are going around, our project stands out as an open source, extensible and also majorly written in Lean leveraging the wonderful metaprogramming framework of Lean. Autoformalisation is achieved by writing various handlers for different kinds of mathematical constructs and composing those handlers to generate the final output. We call this novel approach *Combinator Code Generation*. LeanAide is architected such that any improvements in rule-based automations (for eg `grind`) and large language models would directly improve its autoformalisation capabilities. 

**Funding.** We gratefully acknowledge funding from Renaissance Philanthropy
under their AI for Math Fund.
