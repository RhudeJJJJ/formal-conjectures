/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4111 : Family 8 := level8.get ⟨64,by decide⟩
def sourceMap4111 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4111 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4111_checked : acceptsGraphIso
    (source (graph core4111) (root 8) 2 2) DegreeTwoThreeSpectrum3577.graph sourceMap4111=true := by decide +kernel
theorem fusedMap4111_checked : acceptsGraphIso
    (fused (graph core4111) (root 8) 2 2) DegreeTwoThreeSpectrum2363.graph fusedMap4111=true := by decide +kernel
theorem certified4111 : Certified (graph core4111) (root 8) 2 2 :=
  of_native_maps core4111 DegreeTwoThreeSpectrum3577.graph DegreeTwoThreeSpectrum2363.graph
    sourceMap4111 fusedMap4111 sourceMap4111_checked fusedMap4111_checked
    DegreeTwoThreeFiniteComparisons.comparison4111
#print axioms sourceMap4111_checked
#print axioms fusedMap4111_checked
#print axioms certified4111
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
