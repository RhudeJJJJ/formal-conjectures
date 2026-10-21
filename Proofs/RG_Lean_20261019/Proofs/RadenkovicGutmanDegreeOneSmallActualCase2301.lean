/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2301 : Family 10 := level10.get ⟨936,by decide⟩
def sourceMap2301 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![4,0,9,10,11,12,1,2,3,7,8,5,6] (sourceLabel 10 0 0 v)
def fusedMap2301 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,4,5,6,7,8,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2301_checked : acceptsGraphIso
    (source (graph core2301) (root 10) 0 0) DegreeOneSmallSpectrum1469.graph sourceMap2301=true := by decide +kernel
theorem fusedMap2301_checked : acceptsGraphIso
    (fused (graph core2301) (root 10) 0 0) DegreeOneSmallSpectrum1457.graph fusedMap2301=true := by decide +kernel
theorem certified2301 : Certified (graph core2301) (root 10) 0 0 :=
  of_native_maps core2301 DegreeOneSmallSpectrum1469.graph DegreeOneSmallSpectrum1457.graph
    sourceMap2301 fusedMap2301 sourceMap2301_checked fusedMap2301_checked
    DegreeOneSmallComparisons.comparison2301
#print axioms sourceMap2301_checked
#print axioms fusedMap2301_checked
#print axioms certified2301
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
