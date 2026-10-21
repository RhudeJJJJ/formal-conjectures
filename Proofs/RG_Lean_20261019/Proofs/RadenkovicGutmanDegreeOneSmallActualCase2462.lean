/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2462 : Family 10 := level10.get ⟨1534,by decide⟩
def sourceMap2462 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2462 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2462_checked : acceptsGraphIso
    (source (graph core2462) (root 10) 0 0) DegreeOneSmallSpectrum1997.graph sourceMap2462=true := by decide +kernel
theorem fusedMap2462_checked : acceptsGraphIso
    (fused (graph core2462) (root 10) 0 0) DegreeOneSmallSpectrum1537.graph fusedMap2462=true := by decide +kernel
theorem certified2462 : Certified (graph core2462) (root 10) 0 0 :=
  of_native_maps core2462 DegreeOneSmallSpectrum1997.graph DegreeOneSmallSpectrum1537.graph
    sourceMap2462 fusedMap2462 sourceMap2462_checked fusedMap2462_checked
    DegreeOneSmallComparisons.comparison2462
#print axioms sourceMap2462_checked
#print axioms fusedMap2462_checked
#print axioms certified2462
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
