/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4440 : Family 10 := level10.get ⟨51,by decide⟩
def sourceMap4440 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,11,12,13,14,15,16,9,10,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4440 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (fusedLabel 10 2 2 v)
theorem sourceMap4440_checked : acceptsGraphIso
    (source (graph core4440) (root 10) 2 2) DegreeTwoThreeSpectrum5655.graph sourceMap4440=true := by decide +kernel
theorem fusedMap4440_checked : acceptsGraphIso
    (fused (graph core4440) (root 10) 2 2) DegreeTwoThreeSpectrum5128.graph fusedMap4440=true := by decide +kernel
theorem certified4440 : Certified (graph core4440) (root 10) 2 2 :=
  of_native_maps core4440 DegreeTwoThreeSpectrum5655.graph DegreeTwoThreeSpectrum5128.graph
    sourceMap4440 fusedMap4440 sourceMap4440_checked fusedMap4440_checked
    DegreeTwoThreeFiniteComparisons.comparison4440
#print axioms sourceMap4440_checked
#print axioms fusedMap4440_checked
#print axioms certified4440
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
