/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4851 : Family 10 := level10.get ⟨1255,by decide⟩
def sourceMap4851 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4851 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4851_checked : acceptsGraphIso
    (source (graph core4851) (root 10) 2 2) DegreeTwoThreeSpectrum7337.graph sourceMap4851=true := by decide +kernel
theorem fusedMap4851_checked : acceptsGraphIso
    (fused (graph core4851) (root 10) 2 2) DegreeTwoThreeSpectrum6500.graph fusedMap4851=true := by decide +kernel
theorem certified4851 : Certified (graph core4851) (root 10) 2 2 :=
  of_native_maps core4851 DegreeTwoThreeSpectrum7337.graph DegreeTwoThreeSpectrum6500.graph
    sourceMap4851 fusedMap4851 sourceMap4851_checked fusedMap4851_checked
    DegreeTwoThreeFiniteComparisons.comparison4851
#print axioms sourceMap4851_checked
#print axioms fusedMap4851_checked
#print axioms certified4851
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
