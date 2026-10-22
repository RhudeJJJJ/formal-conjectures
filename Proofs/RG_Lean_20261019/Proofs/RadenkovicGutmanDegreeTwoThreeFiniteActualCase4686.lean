/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4686 : Family 10 := level10.get ⟨842,by decide⟩
def sourceMap4686 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4686 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4686_checked : acceptsGraphIso
    (source (graph core4686) (root 10) 2 2) DegreeTwoThreeSpectrum7523.graph sourceMap4686=true := by decide +kernel
theorem fusedMap4686_checked : acceptsGraphIso
    (fused (graph core4686) (root 10) 2 2) DegreeTwoThreeSpectrum5674.graph fusedMap4686=true := by decide +kernel
theorem certified4686 : Certified (graph core4686) (root 10) 2 2 :=
  of_native_maps core4686 DegreeTwoThreeSpectrum7523.graph DegreeTwoThreeSpectrum5674.graph
    sourceMap4686 fusedMap4686 sourceMap4686_checked fusedMap4686_checked
    DegreeTwoThreeFiniteComparisons.comparison4686
#print axioms sourceMap4686_checked
#print axioms fusedMap4686_checked
#print axioms certified4686
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
