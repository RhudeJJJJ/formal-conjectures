/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4933 : Family 10 := level10.get ⟨1446,by decide⟩
def sourceMap4933 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,7,8,9,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap4933 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4933_checked : acceptsGraphIso
    (source (graph core4933) (root 10) 2 2) DegreeTwoThreeSpectrum7493.graph sourceMap4933=true := by decide +kernel
theorem fusedMap4933_checked : acceptsGraphIso
    (fused (graph core4933) (root 10) 2 2) DegreeTwoThreeSpectrum6911.graph fusedMap4933=true := by decide +kernel
theorem certified4933 : Certified (graph core4933) (root 10) 2 2 :=
  of_native_maps core4933 DegreeTwoThreeSpectrum7493.graph DegreeTwoThreeSpectrum6911.graph
    sourceMap4933 fusedMap4933 sourceMap4933_checked fusedMap4933_checked
    DegreeTwoThreeFiniteComparisons.comparison4933
#print axioms sourceMap4933_checked
#print axioms fusedMap4933_checked
#print axioms certified4933
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
