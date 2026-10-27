/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4785 : Family 10 := level10.get ⟨1089,by decide⟩
def sourceMap4785 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4785 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4785_checked : acceptsGraphIso
    (source (graph core4785) (root 10) 2 2) DegreeTwoThreeSpectrum7168.graph sourceMap4785=true := by decide +kernel
theorem fusedMap4785_checked : acceptsGraphIso
    (fused (graph core4785) (root 10) 2 2) DegreeTwoThreeSpectrum6161.graph fusedMap4785=true := by decide +kernel
theorem certified4785 : Certified (graph core4785) (root 10) 2 2 :=
  of_native_maps core4785 DegreeTwoThreeSpectrum7168.graph DegreeTwoThreeSpectrum6161.graph
    sourceMap4785 fusedMap4785 sourceMap4785_checked fusedMap4785_checked
    DegreeTwoThreeFiniteComparisons.comparison4785
#print axioms sourceMap4785_checked
#print axioms fusedMap4785_checked
#print axioms certified4785
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
