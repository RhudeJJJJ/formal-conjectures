/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4854 : Family 10 := level10.get ⟨1263,by decide⟩
def sourceMap4854 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4854 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4854_checked : acceptsGraphIso
    (source (graph core4854) (root 10) 2 2) DegreeTwoThreeSpectrum7345.graph sourceMap4854=true := by decide +kernel
theorem fusedMap4854_checked : acceptsGraphIso
    (fused (graph core4854) (root 10) 2 2) DegreeTwoThreeSpectrum6515.graph fusedMap4854=true := by decide +kernel
theorem certified4854 : Certified (graph core4854) (root 10) 2 2 :=
  of_native_maps core4854 DegreeTwoThreeSpectrum7345.graph DegreeTwoThreeSpectrum6515.graph
    sourceMap4854 fusedMap4854 sourceMap4854_checked fusedMap4854_checked
    DegreeTwoThreeFiniteComparisons.comparison4854
#print axioms sourceMap4854_checked
#print axioms fusedMap4854_checked
#print axioms certified4854
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
