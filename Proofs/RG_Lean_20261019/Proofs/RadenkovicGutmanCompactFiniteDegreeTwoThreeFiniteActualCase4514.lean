/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4514 : Family 10 := level10.get ⟨339,by decide⟩
def sourceMap4514 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4514 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4514_checked : acceptsGraphIso
    (source (graph core4514) (root 10) 2 2) DegreeTwoThreeSpectrum6743.graph sourceMap4514=true := by decide +kernel
theorem fusedMap4514_checked : acceptsGraphIso
    (fused (graph core4514) (root 10) 2 2) DegreeTwoThreeSpectrum5591.graph fusedMap4514=true := by decide +kernel
theorem certified4514 : Certified (graph core4514) (root 10) 2 2 :=
  of_native_maps core4514 DegreeTwoThreeSpectrum6743.graph DegreeTwoThreeSpectrum5591.graph
    sourceMap4514 fusedMap4514 sourceMap4514_checked fusedMap4514_checked
    DegreeTwoThreeFiniteComparisons.comparison4514
#print axioms sourceMap4514_checked
#print axioms fusedMap4514_checked
#print axioms certified4514
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
