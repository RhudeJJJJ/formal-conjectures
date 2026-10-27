/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4583 : Family 10 := level10.get ⟨550,by decide⟩
def sourceMap4583 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,15,16,14,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4583 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4583_checked : acceptsGraphIso
    (source (graph core4583) (root 10) 2 2) DegreeTwoThreeSpectrum7171.graph sourceMap4583=true := by decide +kernel
theorem fusedMap4583_checked : acceptsGraphIso
    (fused (graph core4583) (root 10) 2 2) DegreeTwoThreeSpectrum5204.graph fusedMap4583=true := by decide +kernel
theorem certified4583 : Certified (graph core4583) (root 10) 2 2 :=
  of_native_maps core4583 DegreeTwoThreeSpectrum7171.graph DegreeTwoThreeSpectrum5204.graph
    sourceMap4583 fusedMap4583 sourceMap4583_checked fusedMap4583_checked
    DegreeTwoThreeFiniteComparisons.comparison4583
#print axioms sourceMap4583_checked
#print axioms fusedMap4583_checked
#print axioms certified4583
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
