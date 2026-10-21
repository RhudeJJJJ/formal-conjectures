/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2323 : Family 10 := level10.get ⟨1016,by decide⟩
def sourceMap2323 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2323 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2323_checked : acceptsGraphIso
    (source (graph core2323) (root 10) 0 0) DegreeOneSmallSpectrum1579.graph sourceMap2323=true := by decide +kernel
theorem fusedMap2323_checked : acceptsGraphIso
    (fused (graph core2323) (root 10) 0 0) DegreeOneSmallSpectrum1585.graph fusedMap2323=true := by decide +kernel
theorem certified2323 : Certified (graph core2323) (root 10) 0 0 :=
  of_native_maps core2323 DegreeOneSmallSpectrum1579.graph DegreeOneSmallSpectrum1585.graph
    sourceMap2323 fusedMap2323 sourceMap2323_checked fusedMap2323_checked
    DegreeOneSmallComparisons.comparison2323
#print axioms sourceMap2323_checked
#print axioms fusedMap2323_checked
#print axioms certified2323
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
