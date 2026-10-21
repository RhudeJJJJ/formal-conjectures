/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2464 : Family 10 := level10.get ⟨1543,by decide⟩
def sourceMap2464 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (sourceLabel 10 0 0 v)
def fusedMap2464 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2464_checked : acceptsGraphIso
    (source (graph core2464) (root 10) 0 0) DegreeOneSmallSpectrum1999.graph sourceMap2464=true := by decide +kernel
theorem fusedMap2464_checked : acceptsGraphIso
    (fused (graph core2464) (root 10) 0 0) DegreeOneSmallSpectrum1555.graph fusedMap2464=true := by decide +kernel
theorem certified2464 : Certified (graph core2464) (root 10) 0 0 :=
  of_native_maps core2464 DegreeOneSmallSpectrum1999.graph DegreeOneSmallSpectrum1555.graph
    sourceMap2464 fusedMap2464 sourceMap2464_checked fusedMap2464_checked
    DegreeOneSmallComparisons.comparison2464
#print axioms sourceMap2464_checked
#print axioms fusedMap2464_checked
#print axioms certified2464
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
