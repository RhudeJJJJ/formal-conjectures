/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2419 : Family 10 := level10.get ⟨1301,by decide⟩
def sourceMap2419 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,4,5,2,3] (sourceLabel 10 0 0 v)
def fusedMap2419 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2419_checked : acceptsGraphIso
    (source (graph core2419) (root 10) 0 0) DegreeOneSmallSpectrum1802.graph sourceMap2419=true := by decide +kernel
theorem fusedMap2419_checked : acceptsGraphIso
    (fused (graph core2419) (root 10) 0 0) DegreeOneSmallSpectrum1939.graph fusedMap2419=true := by decide +kernel
theorem certified2419 : Certified (graph core2419) (root 10) 0 0 :=
  of_native_maps core2419 DegreeOneSmallSpectrum1802.graph DegreeOneSmallSpectrum1939.graph
    sourceMap2419 fusedMap2419 sourceMap2419_checked fusedMap2419_checked
    DegreeOneSmallComparisons.comparison2419
#print axioms sourceMap2419_checked
#print axioms fusedMap2419_checked
#print axioms certified2419
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
