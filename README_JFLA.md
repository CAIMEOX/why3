Ce dépôt a pour objectif de servir de support à l'article 'Des transformations
logiques passent leur certificat' soumis aux JFLA 2020.

Installation
------------

On donne ici un guide pour installer Why3 et tester le plugin du papier.

À la racine du dépôt, faire :

  autoconf
  automake --add-missing

Vous pouvez ignorer les éventuelles erreurs affichées à l'écran à ce stade.

Puis :

  ./configure --enable-local
  make -j

À ce stade, un éxecutable peut être appelé par './bin/why3' ce qui sera abrégé dans la suite
simplement en 'why3'.

Pour pouvoir utiliser Why3 pleinement il est recommandé d'installer au moins Z3, CVC4 et Alt-Ergo.
Dans tous les cas il faut faire :
  why3 config --detect

Pour pouvoir utiliser le vérificateur Dedukti, il faut aussi avoir 'dkcheck' dans le path de
votre système. Une version de Dedukti compatible avec notre plugin est disponible
à l'adresse :
  https://github.com/Deducteam/Dedukti


Accéder au développement du plugin
----------------------------------

Le code source est dans le répertoire ./plugin/cert et est constitué essentiellement
de 5 fichiers :
   - cert_syntax.ml, le fichier qui donne le type des ctask, des certificats et qui
     définit la traduction des tâches Why3 vers les ctask
   - cert_transformations.ml, le fichier qui définit des transformations certifiantes
   - cert_register.ml, le fichier qui, étant donné un checker, fait connaitre à Why3
     les transformations de cert_transformations.ml
   - cert_verif_caml.ml, le fichier qui définit le checker OCaml
   - cert_verif_dedukti.ml, le fichier qui définit le checker Dedukti

Ce dossier contient aussi le jeu de test 'test', que l'on peut lancer avec :
  why3 ide test

Les transformations sont accessibles dans Why3 avec les conventions de nom suivantes :
    Les noms des transformations qui sont vérifiées par OCaml se terminent par '_ccert'.
    Les noms des transformations qui sont vérifiées par Dedukti se terminent par '_dcert'.
Pour savoir quelles transformations sont ainsi accessibles, regarder le fichier
cert_register.ml ou plus simplement taper '_ccert' ou '_dcert' dans Why3.



