/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4889 : Family 10 := level10.get ⟨1346,by decide⟩
def sourceMap4889 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4889 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4889_checked : acceptsGraphIso
    (source (graph core4889) (root 10) 2 2) DegreeTwoThreeSpectrum7425.graph sourceMap4889=true := by decide +kernel
theorem fusedMap4889_checked : acceptsGraphIso
    (fused (graph core4889) (root 10) 2 2) DegreeTwoThreeSpectrum6675.graph fusedMap4889=true := by decide +kernel
theorem certified4889 : Certified (graph core4889) (root 10) 2 2 :=
  of_native_maps core4889 DegreeTwoThreeSpectrum7425.graph DegreeTwoThreeSpectrum6675.graph
    sourceMap4889 fusedMap4889 sourceMap4889_checked fusedMap4889_checked
    DegreeTwoThreeFiniteComparisons.comparison4889
#print axioms sourceMap4889_checked
#print axioms fusedMap4889_checked
#print axioms certified4889
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
