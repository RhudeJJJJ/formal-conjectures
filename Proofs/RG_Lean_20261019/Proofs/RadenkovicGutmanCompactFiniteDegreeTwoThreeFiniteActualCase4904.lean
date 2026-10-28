/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4904 : Family 10 := level10.get ⟨1378,by decide⟩
def sourceMap4904 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4904 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4904_checked : acceptsGraphIso
    (source (graph core4904) (root 10) 2 2) DegreeTwoThreeSpectrum7462.graph sourceMap4904=true := by decide +kernel
theorem fusedMap4904_checked : acceptsGraphIso
    (fused (graph core4904) (root 10) 2 2) DegreeTwoThreeSpectrum6728.graph fusedMap4904=true := by decide +kernel
theorem certified4904 : Certified (graph core4904) (root 10) 2 2 :=
  of_native_maps core4904 DegreeTwoThreeSpectrum7462.graph DegreeTwoThreeSpectrum6728.graph
    sourceMap4904 fusedMap4904 sourceMap4904_checked fusedMap4904_checked
    DegreeTwoThreeFiniteComparisons.comparison4904
#print axioms sourceMap4904_checked
#print axioms fusedMap4904_checked
#print axioms certified4904
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
