/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2335 : Family 10 := level10.get ⟨1041,by decide⟩
def sourceMap2335 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2335 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2335_checked : acceptsGraphIso
    (source (graph core2335) (root 10) 0 0) DegreeOneSmallSpectrum1631.graph sourceMap2335=true := by decide +kernel
theorem fusedMap2335_checked : acceptsGraphIso
    (fused (graph core2335) (root 10) 0 0) DegreeOneSmallSpectrum1637.graph fusedMap2335=true := by decide +kernel
theorem certified2335 : Certified (graph core2335) (root 10) 0 0 :=
  of_native_maps core2335 DegreeOneSmallSpectrum1631.graph DegreeOneSmallSpectrum1637.graph
    sourceMap2335 fusedMap2335 sourceMap2335_checked fusedMap2335_checked
    DegreeOneSmallComparisons.comparison2335
#print axioms sourceMap2335_checked
#print axioms fusedMap2335_checked
#print axioms certified2335
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
