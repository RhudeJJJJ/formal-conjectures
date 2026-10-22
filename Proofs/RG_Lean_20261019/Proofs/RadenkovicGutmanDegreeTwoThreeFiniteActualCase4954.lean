/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4954 : Family 10 := level10.get ⟨1497,by decide⟩
def sourceMap4954 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4954 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4954_checked : acceptsGraphIso
    (source (graph core4954) (root 10) 2 2) DegreeTwoThreeSpectrum7196.graph sourceMap4954=true := by decide +kernel
theorem fusedMap4954_checked : acceptsGraphIso
    (fused (graph core4954) (root 10) 2 2) DegreeTwoThreeSpectrum7001.graph fusedMap4954=true := by decide +kernel
theorem certified4954 : Certified (graph core4954) (root 10) 2 2 :=
  of_native_maps core4954 DegreeTwoThreeSpectrum7196.graph DegreeTwoThreeSpectrum7001.graph
    sourceMap4954 fusedMap4954 sourceMap4954_checked fusedMap4954_checked
    DegreeTwoThreeFiniteComparisons.comparison4954
#print axioms sourceMap4954_checked
#print axioms fusedMap4954_checked
#print axioms certified4954
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
