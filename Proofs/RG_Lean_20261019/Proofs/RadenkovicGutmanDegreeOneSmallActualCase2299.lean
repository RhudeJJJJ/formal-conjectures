/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2299 : Family 10 := level10.get ⟨933,by decide⟩
def sourceMap2299 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,9,10,11,12,1,2,3,4,8,6,7] (sourceLabel 10 0 0 v)
def fusedMap2299 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,9,10,11,12,1,2,3,4,8,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2299_checked : acceptsGraphIso
    (source (graph core2299) (root 10) 0 0) DegreeOneSmallSpectrum1400.graph sourceMap2299=true := by decide +kernel
theorem fusedMap2299_checked : acceptsGraphIso
    (fused (graph core2299) (root 10) 0 0) DegreeOneSmallSpectrum1395.graph fusedMap2299=true := by decide +kernel
theorem certified2299 : Certified (graph core2299) (root 10) 0 0 :=
  of_native_maps core2299 DegreeOneSmallSpectrum1400.graph DegreeOneSmallSpectrum1395.graph
    sourceMap2299 fusedMap2299 sourceMap2299_checked fusedMap2299_checked
    DegreeOneSmallComparisons.comparison2299
#print axioms sourceMap2299_checked
#print axioms fusedMap2299_checked
#print axioms certified2299
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
