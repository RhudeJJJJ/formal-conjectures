/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4868 : Family 10 := level10.get ⟨1292,by decide⟩
def sourceMap4868 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4868 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4868_checked : acceptsGraphIso
    (source (graph core4868) (root 10) 2 2) DegreeTwoThreeSpectrum7372.graph sourceMap4868=true := by decide +kernel
theorem fusedMap4868_checked : acceptsGraphIso
    (fused (graph core4868) (root 10) 2 2) DegreeTwoThreeSpectrum6569.graph fusedMap4868=true := by decide +kernel
theorem certified4868 : Certified (graph core4868) (root 10) 2 2 :=
  of_native_maps core4868 DegreeTwoThreeSpectrum7372.graph DegreeTwoThreeSpectrum6569.graph
    sourceMap4868 fusedMap4868 sourceMap4868_checked fusedMap4868_checked
    DegreeTwoThreeFiniteComparisons.comparison4868
#print axioms sourceMap4868_checked
#print axioms fusedMap4868_checked
#print axioms certified4868
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
