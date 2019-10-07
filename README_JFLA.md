Ce dépôt sert de support à l'article 'Des transformations
logiques passent leur certificat' soumis aux [JFLA 2020](http://jfla.inria.fr/jfla2020.html).

Compilation
-----------

On donne ici un guide pour compiler Why3 et tester le greffon décrit dans l'article.

La compilation nécessite une version récente d'OCaml et de menhir.

À la racine du dépôt, faire :
```shell
autoconf
automake --add-missing
```

Vous pouvez ignorer les éventuelles erreurs affichées à l'écran à ce stade.

Puis :

```shell
./configure --enable-local
make -j
```

À ce stade, un éxecutable peut être appelé par `bin/why3`.

Pour pouvoir utiliser Why3 pleinement il est recommandé d'installer au moins Z3, CVC4 et Alt-Ergo.
Dans tous les cas il faut faire :
```shell
bin/why3 config --detect
```

Pour pouvoir utiliser le vérificateur Dedukti, il faut aussi avoir `dkcheck` dans le path de
votre système. Une version de Dedukti compatible avec notre plugin est disponible
à [ici](https://github.com/Deducteam/Dedukti).



Utilisation
-----------

Les transformations sont accessibles dans Why3 avec les conventions de noms suivantes :
  - Les noms des transformations qui sont vérifiées par OCaml se terminent par `_ccert`.
  - Les noms des transformations qui sont vérifiées par Dedukti se terminent par `_dcert`.
Pour savoir quelles transformations sont ainsi accessibles, regarder le fichier
`cert_register.ml` ou plus simplement taper `_ccert` ou `_dcert` dans l'invite de commande Why3.

Pour lancer le jeu de tests du plugin, faire :
```shell
bin/why3 ide test
```



Accéder au développement du plugin
----------------------------------

Le code source est dans le répertoire `plugin/cert` et est constitué essentiellement
de 5 fichiers :
   - le fichier `cert_syntax.ml` donne le type des `ctask` et des certificats, et
     définit la traduction des tâches Why3 vers les `ctask`
   - le fichier `cert_transformations.ml` définit les transformations certifiantes
   - le fichier `cert_register.ml`, étant donné un vérificateur, fait connaitre à Why3
     les transformations de `cert_transformations.ml`
   - le fichier `cert_verif_caml.ml` définit le vérificateur OCaml
   - le fichier `cert_verif_dedukti.ml` définit le vérificateur Dedukti
