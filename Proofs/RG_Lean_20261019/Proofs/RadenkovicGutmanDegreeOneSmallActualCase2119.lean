/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2119 : Family 10 := level10.get ⟨549,by decide⟩
def sourceMap2119 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2119 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2119_checked : acceptsGraphIso
    (source (graph core2119) (root 10) 0 0) DegreeOneSmallSpectrum1674.graph sourceMap2119=true := by decide +kernel
theorem fusedMap2119_checked : acceptsGraphIso
    (fused (graph core2119) (root 10) 0 0) DegreeOneSmallSpectrum1076.graph fusedMap2119=true := by decide +kernel
theorem certified2119 : Certified (graph core2119) (root 10) 0 0 :=
  of_native_maps core2119 DegreeOneSmallSpectrum1674.graph DegreeOneSmallSpectrum1076.graph
    sourceMap2119 fusedMap2119 sourceMap2119_checked fusedMap2119_checked
    DegreeOneSmallComparisons.comparison2119
#print axioms sourceMap2119_checked
#print axioms fusedMap2119_checked
#print axioms certified2119
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
