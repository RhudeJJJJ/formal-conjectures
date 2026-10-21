/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2032 : Family 10 := level10.get ⟨385,by decide⟩
def sourceMap2032 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2032 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2032_checked : acceptsGraphIso
    (source (graph core2032) (root 10) 0 0) DegreeOneSmallSpectrum1109.graph sourceMap2032=true := by decide +kernel
theorem fusedMap2032_checked : acceptsGraphIso
    (fused (graph core2032) (root 10) 0 0) DegreeOneSmallSpectrum1486.graph fusedMap2032=true := by decide +kernel
theorem certified2032 : Certified (graph core2032) (root 10) 0 0 :=
  of_native_maps core2032 DegreeOneSmallSpectrum1109.graph DegreeOneSmallSpectrum1486.graph
    sourceMap2032 fusedMap2032 sourceMap2032_checked fusedMap2032_checked
    DegreeOneSmallComparisons.comparison2032
#print axioms sourceMap2032_checked
#print axioms fusedMap2032_checked
#print axioms certified2032
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
