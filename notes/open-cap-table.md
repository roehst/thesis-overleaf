OCF (or Open Cap Table Format) is an open source data standard for company capitalization data developed by the Open Cap Table Coalition to enable the easy and accurate exchange and use of company capitalization information through a standardized format.

OCF is a JSON-based format, wherein individual objects required to describe a company cap table are stored in JSONs that match our OCF JSON Schemas. Our reference implementation suggests storing these JSONs in a specific set of files in a zip archive, but OCF-compatible data could be provided via API as well. Please see our documentation for more details on JSON Schema, OCF's schemas or how to use them.

> OCF is designed to be extremely expressive and extensible. 
> OCF is powered by an event-driven architecture. These events describe the relevant data needed to describe key events such as issuances, transfers, conversions, etc.
> The conversion of one OCF security into another is modeled using three key concepts which describe how, when and into what a convertible security converts into:
> Conversion Right: what can the security convert into?
> Conversion Trigger: when and under what conditions does the Conversion Right come into effect?
> Conversion Mechanism: how is the coversion amount calculated?