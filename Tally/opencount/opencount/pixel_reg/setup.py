from distutils.core import setup
from distutils.extension import Extension
from Cython.Distutils import build_ext

ext_modules = [Extension("distance_transform", ["distance_transform.pyx"]),Extension("imagesAlign1_cy", ["imagesAlign1_cy.pyx"])]

setup(
    name = 'pixel reg stuff',
    cmdclass = {'build_ext': build_ext},
    ext_modules = ext_modules
)
