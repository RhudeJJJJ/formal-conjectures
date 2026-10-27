/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4543 : Family 10 := level10.get ⟨425,by decide⟩
def sourceMap4543 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,8,9,10,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4543 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 2 2 v)
theorem sourceMap4543_checked : acceptsGraphIso
    (source (graph core4543) (root 10) 2 2) DegreeTwoThreeSpectrum6801.graph sourceMap4543=true := by decide +kernel
theorem fusedMap4543_checked : acceptsGraphIso
    (fused (graph core4543) (root 10) 2 2) DegreeTwoThreeSpectrum5816.graph fusedMap4543=true := by decide +kernel
theorem certified4543 : Certified (graph core4543) (root 10) 2 2 :=
  of_native_maps core4543 DegreeTwoThreeSpectrum6801.graph DegreeTwoThreeSpectrum5816.graph
    sourceMap4543 fusedMap4543 sourceMap4543_checked fusedMap4543_checked
    DegreeTwoThreeFiniteComparisons.comparison4543
#print axioms sourceMap4543_checked
#print axioms fusedMap4543_checked
#print axioms certified4543
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
