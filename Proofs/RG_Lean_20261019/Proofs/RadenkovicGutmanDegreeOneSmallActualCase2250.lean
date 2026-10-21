/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2250 : Family 10 := level10.get ⟨808,by decide⟩
def sourceMap2250 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2250 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2250_checked : acceptsGraphIso
    (source (graph core2250) (root 10) 0 0) DegreeOneSmallSpectrum1732.graph sourceMap2250=true := by decide +kernel
theorem fusedMap2250_checked : acceptsGraphIso
    (fused (graph core2250) (root 10) 0 0) DegreeOneSmallSpectrum1443.graph fusedMap2250=true := by decide +kernel
theorem certified2250 : Certified (graph core2250) (root 10) 0 0 :=
  of_native_maps core2250 DegreeOneSmallSpectrum1732.graph DegreeOneSmallSpectrum1443.graph
    sourceMap2250 fusedMap2250 sourceMap2250_checked fusedMap2250_checked
    DegreeOneSmallComparisons.comparison2250
#print axioms sourceMap2250_checked
#print axioms fusedMap2250_checked
#print axioms certified2250
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
