_Typing Flags_ is a Coq plugin to disable positivity check, guard check and termination check.

Disabling those checks leads of course to inconsistencies, use it at your own risks ...

This plugin is not perfect but it does the job. A better integration in Coq should arrive at some point.



Usage
=====

This plugin provides the following commands:

- `Set Type In Type`
  Globally enable "type in type", meaning that all "Type@{i}" are convertible. Prop and Set remain distinct.

- `Unset Type In Type`
  Disable "type in type".

- `Unset Guard Checking`
  Disable the positivity checking of inductive types and the termination checking of fixpoints.

- `Set Guard Checking`
  (Re)enable positivity and termination checking. Note that a fixpoint defined unguarded may be re-type checked if it is unfolded for a reason or another (Does anybody have a nice example?)

- `Print Typing Flags`
  Print the status of typing flags.

The `Print Assumptions` command keeps track of which definition and inductives are unsafe. The command `About` also prints safety datas.


Installation
============

Run `make` to compile the plugin, it needs to have `coqc` available.

Then, provided the repository theories of the plugin is in your load path, load it with:

`Require Import TypingFlags.Loader.`

To copy the plugin in the contrib directory of your local installation of Coq, and thus make it always available simply run:

`make install`

Tested with coq 8.6, 8.7, 8.8, master June 2018.


Examples
========

- `theories/Demo.v`

- `theories/BreadthFirst.v`
  Implementation of Martin Hofmann breadthfirst algorithm, presented by Ralph Matthes in TYPES 2018.


Acknowledgments
===============

This plugin does not implement anything and only make accessible to the user some hidden functionalities of Coq. The implementation is due to Coq developers and in particular Arnaud Spiwack.

References: https://github.com/coq/coq/pull/79, https://github.com/coq/coq/pull/7651


Feedback and other use cases welcome.
