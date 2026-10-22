/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4841 : Family 10 := level10.get ⟨1225,by decide⟩
def sourceMap4841 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4841 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4841_checked : acceptsGraphIso
    (source (graph core4841) (root 10) 2 2) DegreeTwoThreeSpectrum7147.graph sourceMap4841=true := by decide +kernel
theorem fusedMap4841_checked : acceptsGraphIso
    (fused (graph core4841) (root 10) 2 2) DegreeTwoThreeSpectrum6426.graph fusedMap4841=true := by decide +kernel
theorem certified4841 : Certified (graph core4841) (root 10) 2 2 :=
  of_native_maps core4841 DegreeTwoThreeSpectrum7147.graph DegreeTwoThreeSpectrum6426.graph
    sourceMap4841 fusedMap4841 sourceMap4841_checked fusedMap4841_checked
    DegreeTwoThreeFiniteComparisons.comparison4841
#print axioms sourceMap4841_checked
#print axioms fusedMap4841_checked
#print axioms certified4841
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
