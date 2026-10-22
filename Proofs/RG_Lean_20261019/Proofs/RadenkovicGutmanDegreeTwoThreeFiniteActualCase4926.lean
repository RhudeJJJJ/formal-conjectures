/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4926 : Family 10 := level10.get ⟨1432,by decide⟩
def sourceMap4926 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9] (sourceLabel 10 2 2 v)
def fusedMap4926 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4926_checked : acceptsGraphIso
    (source (graph core4926) (root 10) 2 2) DegreeTwoThreeSpectrum7476.graph sourceMap4926=true := by decide +kernel
theorem fusedMap4926_checked : acceptsGraphIso
    (fused (graph core4926) (root 10) 2 2) DegreeTwoThreeSpectrum6890.graph fusedMap4926=true := by decide +kernel
theorem certified4926 : Certified (graph core4926) (root 10) 2 2 :=
  of_native_maps core4926 DegreeTwoThreeSpectrum7476.graph DegreeTwoThreeSpectrum6890.graph
    sourceMap4926 fusedMap4926 sourceMap4926_checked fusedMap4926_checked
    DegreeTwoThreeFiniteComparisons.comparison4926
#print axioms sourceMap4926_checked
#print axioms fusedMap4926_checked
#print axioms certified4926
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
