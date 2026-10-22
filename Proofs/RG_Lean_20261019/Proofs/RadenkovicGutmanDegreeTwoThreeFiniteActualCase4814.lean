/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4814 : Family 10 := level10.get ⟨1166,by decide⟩
def sourceMap4814 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4814 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4814_checked : acceptsGraphIso
    (source (graph core4814) (root 10) 2 2) DegreeTwoThreeSpectrum7257.graph sourceMap4814=true := by decide +kernel
theorem fusedMap4814_checked : acceptsGraphIso
    (fused (graph core4814) (root 10) 2 2) DegreeTwoThreeSpectrum6316.graph fusedMap4814=true := by decide +kernel
theorem certified4814 : Certified (graph core4814) (root 10) 2 2 :=
  of_native_maps core4814 DegreeTwoThreeSpectrum7257.graph DegreeTwoThreeSpectrum6316.graph
    sourceMap4814 fusedMap4814 sourceMap4814_checked fusedMap4814_checked
    DegreeTwoThreeFiniteComparisons.comparison4814
#print axioms sourceMap4814_checked
#print axioms fusedMap4814_checked
#print axioms certified4814
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
