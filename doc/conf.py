# Configuration file for the Sphinx documentation builder.
#
# For the full list of built-in configuration values, see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

from datetime import date
from sphinx import addnodes
from docutils import nodes

def setup(app):
    def parse_theorem(env, sig, signode):
        theorem_title = sig
        signode += addnodes.desc_name(theorem_title, theorem_title)
        return sig
    app.add_object_type('theorem', 'theorem', '%s (theorem)', parse_node=parse_theorem)

    def parse_def(env, sig, signode):
        def_title = sig
        # accel_node = nodes.inline()
        # letter_node = nodes.Text(sig)
        # accel_node += letter_node
        # accel_node['classes'].append('lean')
        signode += addnodes.desc_name(def_title, def_title)
        return sig
    app.add_object_type('def', 'def', '%s (def)', parse_node=parse_def)

    def parse_option(env, sig, signode):
        option_title = sig
        signode += addnodes.desc_name(option_title, option_title)
        return sig
    app.add_object_type('option', 'option', '%s (option)', parse_node=parse_option)

# -- Project information -----------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#project-information

project = 'Leanses'
copyright = f'{date.today().year}, Yann Herklotz'
author = 'Yann Herklotz'
release = 'v0.0.1'

# -- General configuration ---------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#general-configuration

extensions = []

templates_path = ['_templates']
exclude_patterns = ['_build', 'Thumbs.db', '.DS_Store']

# -- Options for HTML output -------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#options-for-html-output

html_theme = 'furo'
html_static_path = ['_static']

rst_prolog = """
.. role:: lean(code)
  :language: lean
  :class: highlight
"""
