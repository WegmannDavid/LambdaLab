#!/usr/bin/env python3
"""Package the extension as a .vsix, with nothing but the Python standard library.

A .vsix is a zip: the extension's files under `extension/`, a manifest, and a content-types table.
Run from this directory: python3 package.py — then `code --install-extension lambdalab-<version>.vsix`.
"""
import json
import os
import zipfile

HERE = os.path.dirname(os.path.abspath(__file__))
FILES = ["package.json", "extension.js", "language-configuration.json", "README.md"]

pkg = json.load(open(os.path.join(HERE, "package.json")))
files = FILES + sorted(os.path.join("syntaxes", f) for f in os.listdir(os.path.join(HERE, "syntaxes"))
                       if f.endswith(".tmLanguage.json"))

manifest = f"""<?xml version="1.0" encoding="utf-8"?>
<PackageManifest Version="2.0.0" xmlns="http://schemas.microsoft.com/developer/vsx-schema/2011"
    xmlns:d="http://schemas.microsoft.com/developer/vsx-schema-design/2011">
  <Metadata>
    <Identity Language="en-US" Id="{pkg['name']}" Version="{pkg['version']}" Publisher="{pkg['publisher']}"/>
    <DisplayName>{pkg['displayName']}</DisplayName>
    <Description xml:space="preserve">{pkg['description']}</Description>
    <Categories>Programming Languages</Categories>
    <GalleryFlags>Public</GalleryFlags>
    <Properties>
      <Property Id="Microsoft.VisualStudio.Code.Engine" Value="{pkg['engines']['vscode']}"/>
    </Properties>
  </Metadata>
  <Installation>
    <InstallationTarget Id="Microsoft.VisualStudio.Code"/>
  </Installation>
  <Dependencies/>
  <Assets>
    <Asset Type="Microsoft.VisualStudio.Code.Manifest" Path="extension/package.json" Addressable="true"/>
  </Assets>
</PackageManifest>
"""

content_types = """<?xml version="1.0" encoding="utf-8"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
  <Default Extension=".json" ContentType="application/json"/>
  <Default Extension=".js" ContentType="application/javascript"/>
  <Default Extension=".md" ContentType="text/markdown"/>
  <Default Extension=".vsixmanifest" ContentType="text/xml"/>
</Types>
"""

out = os.path.join(HERE, f"{pkg['name']}-{pkg['version']}.vsix")
with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED) as z:
    z.writestr("extension.vsixmanifest", manifest)
    z.writestr("[Content_Types].xml", content_types)
    for f in files:
        z.write(os.path.join(HERE, f), "extension/" + f.replace(os.sep, "/"))
print(out)
