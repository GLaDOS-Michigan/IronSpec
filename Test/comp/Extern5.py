"""
The Python compiler only supports {:extern} code on a module level, so the
entire module must be supplied.
"""

import sys, _dafny

assert "Library" == __name__
Library = sys.modules[__name__]

class LibClass:
    @staticmethod
    def CallMeInt(x):
        y = x + 1
        z = y + y
        return (y, z)

    @staticmethod
    def CallMeNative(x, b):
        if b:
            y = x + 1
        else:
            y = x - 1
        return y

class OtherClass:
    @staticmethod
    def CallMe():
        return "OtherClass.CallMe"

class AllDafny:
    @staticmethod
    def M():
        _dafny.print(_dafny.Seq("AllDafny.M\n"))

class Mixed:
    def ctor__(self):
        pass

    @staticmethod
    def M():
        _dafny.print(_dafny.Seq("Extern static method says: "))
        Library.Mixed.P()

    @staticmethod
    def P():
        _dafny.print(_dafny.Seq("Mixed.P\n"))

    def IM(self):
        _dafny.print(_dafny.Seq("Extern instance method says: "))
        (self).IP()

    def IP(self):
        _dafny.print(_dafny.Seq("Mixed.IP\n"))

    @staticmethod
    def F():
        return (1000) + (Library.Mixed.G())

    @staticmethod
    def G():
        return 1

    def IF(self):
        return (2000) + ((self).IG())

    def IG(self):
        return 2

class AllExtern:
    @staticmethod
    def P():
        _dafny.print(_dafny.Seq("AllExtern.P\n"))
