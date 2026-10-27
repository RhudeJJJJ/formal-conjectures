/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4759 : Family 10 := level10.get ⟨1026,by decide⟩
def sourceMap4759 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4759 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4759_checked : acceptsGraphIso
    (source (graph core4759) (root 10) 2 2) DegreeTwoThreeSpectrum7103.graph sourceMap4759=true := by decide +kernel
theorem fusedMap4759_checked : acceptsGraphIso
    (fused (graph core4759) (root 10) 2 2) DegreeTwoThreeSpectrum6034.graph fusedMap4759=true := by decide +kernel
theorem certified4759 : Certified (graph core4759) (root 10) 2 2 :=
  of_native_maps core4759 DegreeTwoThreeSpectrum7103.graph DegreeTwoThreeSpectrum6034.graph
    sourceMap4759 fusedMap4759 sourceMap4759_checked fusedMap4759_checked
    DegreeTwoThreeFiniteComparisons.comparison4759
#print axioms sourceMap4759_checked
#print axioms fusedMap4759_checked
#print axioms certified4759
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
