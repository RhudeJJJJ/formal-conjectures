/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4873 : Family 10 := level10.get ⟨1310,by decide⟩
def sourceMap4873 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4873 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4873_checked : acceptsGraphIso
    (source (graph core4873) (root 10) 2 2) DegreeTwoThreeSpectrum7391.graph sourceMap4873=true := by decide +kernel
theorem fusedMap4873_checked : acceptsGraphIso
    (fused (graph core4873) (root 10) 2 2) DegreeTwoThreeSpectrum6607.graph fusedMap4873=true := by decide +kernel
theorem certified4873 : Certified (graph core4873) (root 10) 2 2 :=
  of_native_maps core4873 DegreeTwoThreeSpectrum7391.graph DegreeTwoThreeSpectrum6607.graph
    sourceMap4873 fusedMap4873 sourceMap4873_checked fusedMap4873_checked
    DegreeTwoThreeFiniteComparisons.comparison4873
#print axioms sourceMap4873_checked
#print axioms fusedMap4873_checked
#print axioms certified4873
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
