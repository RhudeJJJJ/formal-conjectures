/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4587 : Family 10 := level10.get ⟨556,by decide⟩
def sourceMap4587 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4587 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4587_checked : acceptsGraphIso
    (source (graph core4587) (root 10) 2 2) DegreeTwoThreeSpectrum7169.graph sourceMap4587=true := by decide +kernel
theorem fusedMap4587_checked : acceptsGraphIso
    (fused (graph core4587) (root 10) 2 2) DegreeTwoThreeSpectrum5214.graph fusedMap4587=true := by decide +kernel
theorem certified4587 : Certified (graph core4587) (root 10) 2 2 :=
  of_native_maps core4587 DegreeTwoThreeSpectrum7169.graph DegreeTwoThreeSpectrum5214.graph
    sourceMap4587 fusedMap4587 sourceMap4587_checked fusedMap4587_checked
    DegreeTwoThreeFiniteComparisons.comparison4587
#print axioms sourceMap4587_checked
#print axioms fusedMap4587_checked
#print axioms certified4587
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
