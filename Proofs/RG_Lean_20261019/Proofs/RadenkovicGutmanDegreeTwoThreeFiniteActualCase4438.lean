/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4438 : Family 10 := level10.get ⟨47,by decide⟩
def sourceMap4438 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,11,12,13,14,15,16,10,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4438 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (fusedLabel 10 2 2 v)
theorem sourceMap4438_checked : acceptsGraphIso
    (source (graph core4438) (root 10) 2 2) DegreeTwoThreeSpectrum5657.graph sourceMap4438=true := by decide +kernel
theorem fusedMap4438_checked : acceptsGraphIso
    (fused (graph core4438) (root 10) 2 2) DegreeTwoThreeSpectrum5131.graph fusedMap4438=true := by decide +kernel
theorem certified4438 : Certified (graph core4438) (root 10) 2 2 :=
  of_native_maps core4438 DegreeTwoThreeSpectrum5657.graph DegreeTwoThreeSpectrum5131.graph
    sourceMap4438 fusedMap4438 sourceMap4438_checked fusedMap4438_checked
    DegreeTwoThreeFiniteComparisons.comparison4438
#print axioms sourceMap4438_checked
#print axioms fusedMap4438_checked
#print axioms certified4438
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
