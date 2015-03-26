How to work with the external replib:

  * To incorporate a new version of replib, for testing, without forcing others to use the new replib (local change):

```
   svn update [-r REV] lib/replib-read-only
```

  * To force everyone to use a different version of replib (global change):

```
   svn propedit svn:externals lib
```

> and change the central -rREV part.  E.g. here's the addition of fixed revision (We use the pre 1.5 externals syntax to support old clients):

```
   Property changes on: lib
   Modified: svn:externals
      - replib-read-only http://replib.googlecode.com/svn/trunk/
      + replib-read-only -r31 http://replib.googlecode.com/svn/trunk/
```

Everything about
[svn:externals](http://svnbook.red-bean.com/en/1.5/svn.advanced.externals.html)