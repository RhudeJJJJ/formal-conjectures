/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4771 : Family 10 := level10.get ⟨1059,by decide⟩
def sourceMap4771 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4771 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4771_checked : acceptsGraphIso
    (source (graph core4771) (root 10) 2 2) DegreeTwoThreeSpectrum7137.graph sourceMap4771=true := by decide +kernel
theorem fusedMap4771_checked : acceptsGraphIso
    (fused (graph core4771) (root 10) 2 2) DegreeTwoThreeSpectrum6103.graph fusedMap4771=true := by decide +kernel
theorem certified4771 : Certified (graph core4771) (root 10) 2 2 :=
  of_native_maps core4771 DegreeTwoThreeSpectrum7137.graph DegreeTwoThreeSpectrum6103.graph
    sourceMap4771 fusedMap4771 sourceMap4771_checked fusedMap4771_checked
    DegreeTwoThreeFiniteComparisons.comparison4771
#print axioms sourceMap4771_checked
#print axioms fusedMap4771_checked
#print axioms certified4771
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
