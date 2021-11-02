Cette branche contient le code source du greffon associé à ma thèse intitulée
'Certification de la transformation d'obligations de preuve'.

Compilation
-----------

Voici les instructions à suivre pour compiler Why3 et tester le greffon.
Cela demande d'avoir accès à une version récente d'OCaml.

À la racine du projet, faire:
```shell
autoconf
./configure --enable-local
make -j
```

À cette étape, il est possible d'appeler le binaire Why3 généré par `bin/why3`.

Pour pouvoir utiliser Why3 pleinement, il est recommandé d'installer au moins
Z3, CVC4 et Alt-Ergo.

Dans tous les cas, il faut ensuite faire:
```shell
bin/why3 config detect
```

Pour pouvoir utiliser les transformations vérifiées par Lambdapi, il faut avoir
`lambdapi` dans le PATH. Pour cela, une possibilité est de suivre les instructions
du [dépôt Lambdapi](https://github.com/Deducteam/lambdapi). Le greffon a été testé
et fonctionne pour la version Lambdapi du [commit
`6b453ab1f1fd0c48bb18ce077009e038c649cf04`.](https://github.com/Deducteam/lambdapi/commit/6b453ab1f1fd0c48bb18ce077009e038c649cf04)


Utilisation
-----

Les transformations certifiantes sont disponibles dans Why3 lorsqu'on lui passe l'option `--cert`.
Elles suivent les conventions de nom suivantes:
  - le nom d'une transformation vérifiée par le vérificateur OCaml se termine par `_ccert`.
  - le nom d'une transformation vérifiée par le vérificateur Lambdapi se termine par `_lcert`.

Ainsi, pour obtenir la liste des transformations certifiantes, il suffit de taper
`_ccert` or `_lcert` dans l'invite de commande de Why3.


Pour lancer l'IDE sur les fichiers de test, on peut faire:
```shell
bin/why3 ide --cert plugins/cert/tests/core
bin/why3 ide --cert plugins/cert/tests/rewrite
bin/why3 ide --cert plugins/cert/tests/induction
```
Le chargement peut prendre quelques secondes en fonction du fichier à charger.

Code source
-----------
Le code source est disponible dans le répertoire `plugin/cert` est est composé, principalement, des fichiers suivants:
   - le fichier `cert_syntax.ml` définit la représentation des termes, des types et des tâches
   - le fichier `cert_abstract.ml` implémente la traduction des tâches de Why3 dans cette représentations
   - le fichier `cert_certificates.ml` définit les certificats et implémente l'élaboration
   - le fichier `cert_trans_util.ml` définit des fonctions utiles pour implémenter des transformations certifiantes
   - le fichier `cert_trans_core.ml` définit diverses transformations certifiantes
   - le fichier `cert_rewrite.ml` définit une version certifiante de la transformation `rewrite`
   - le fichier `cert_induction.ml` définit une version certifiante de la transformation `induction`
   - le fichier `cert_split.ml` définit une version certifiante de la transformation `split`
   - le fichier `cert_verif_caml.ml` implémente le vérificateur OCaml
   - le fichier `cert_verif_lambdapi.ml` implémente le vérificateur Lambdapi
   - le fichier `cert_register.ml` rend accessible dans Why3 les transformations certifiantes

De plus, le fichier `share/lambdapi/preamble.lp` définit l'encodage de CoC dans
Lamdbapi, les extensions de la logique, les théories interprétées et les termes
associés aux règles d'inférence des certificats. Il sert de préambule à la
vérification de typage effectuée par le vérificateur Lambdapi.
