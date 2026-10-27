/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4512 : Family 10 := level10.get ⟨332,by decide⟩
def sourceMap4512 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4512 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4512_checked : acceptsGraphIso
    (source (graph core4512) (root 10) 2 2) DegreeTwoThreeSpectrum6725.graph sourceMap4512=true := by decide +kernel
theorem fusedMap4512_checked : acceptsGraphIso
    (fused (graph core4512) (root 10) 2 2) DegreeTwoThreeSpectrum5572.graph fusedMap4512=true := by decide +kernel
theorem certified4512 : Certified (graph core4512) (root 10) 2 2 :=
  of_native_maps core4512 DegreeTwoThreeSpectrum6725.graph DegreeTwoThreeSpectrum5572.graph
    sourceMap4512 fusedMap4512 sourceMap4512_checked fusedMap4512_checked
    DegreeTwoThreeFiniteComparisons.comparison4512
#print axioms sourceMap4512_checked
#print axioms fusedMap4512_checked
#print axioms certified4512
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
