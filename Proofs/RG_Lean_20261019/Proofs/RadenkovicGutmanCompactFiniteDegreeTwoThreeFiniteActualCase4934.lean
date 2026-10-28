/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4934 : Family 10 := level10.get ⟨1449,by decide⟩
def sourceMap4934 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4934 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4934_checked : acceptsGraphIso
    (source (graph core4934) (root 10) 2 2) DegreeTwoThreeSpectrum7557.graph sourceMap4934=true := by decide +kernel
theorem fusedMap4934_checked : acceptsGraphIso
    (fused (graph core4934) (root 10) 2 2) DegreeTwoThreeSpectrum6916.graph fusedMap4934=true := by decide +kernel
theorem certified4934 : Certified (graph core4934) (root 10) 2 2 :=
  of_native_maps core4934 DegreeTwoThreeSpectrum7557.graph DegreeTwoThreeSpectrum6916.graph
    sourceMap4934 fusedMap4934 sourceMap4934_checked fusedMap4934_checked
    DegreeTwoThreeFiniteComparisons.comparison4934
#print axioms sourceMap4934_checked
#print axioms fusedMap4934_checked
#print axioms certified4934
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
