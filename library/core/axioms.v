Require Export FunctionalExtensionality.
Require Export PropExtensionality.

Ltac rel_ext :=
  apply functional_extensionality; intro;
  apply functional_extensionality; intro;
  apply propositional_extensionality; split.