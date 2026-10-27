/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4739 : Family 10 := level10.get ⟨970,by decide⟩
def sourceMap4739 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,8,9,10,11,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4739 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4739_checked : acceptsGraphIso
    (source (graph core4739) (root 10) 2 2) DegreeTwoThreeSpectrum7490.graph sourceMap4739=true := by decide +kernel
theorem fusedMap4739_checked : acceptsGraphIso
    (fused (graph core4739) (root 10) 2 2) DegreeTwoThreeSpectrum5890.graph fusedMap4739=true := by decide +kernel
theorem certified4739 : Certified (graph core4739) (root 10) 2 2 :=
  of_native_maps core4739 DegreeTwoThreeSpectrum7490.graph DegreeTwoThreeSpectrum5890.graph
    sourceMap4739 fusedMap4739 sourceMap4739_checked fusedMap4739_checked
    DegreeTwoThreeFiniteComparisons.comparison4739
#print axioms sourceMap4739_checked
#print axioms fusedMap4739_checked
#print axioms certified4739
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
